#from functools import reduce
import string
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
#from sage.modules.free_module import VectorSpace
#from sage.rings.big_oh import O
#from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.all import NumberField, pari, random_prime, Set, next_prime
from sage.functions.other import ceil, floor
#from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from BinarySexticsCovariants import EvaluateBasicCovariants, ListOfWeights, RingOfCovariants
from DimFormulaSMFScalarValuedLevel1WithoutCharacter import dim_splitting_SV_All_weight
from DimFormulaSMFVectorValuedLevel1WithoutCharacter import dim_splitting_VV_All_weight
from DimFormulaSMFScalarValuedLevel1WithCharacter import dim_splitting_SV_All_weight_charac
from DimFormulaSMFVectorValuedLevel1WithCharacter import dim_splitting_VV_All_weight_charac
#from FJexp import VectorFJexp, FJexp
from ThetaFourier import Chi
#from Generators_Ring_Covariants_Sextic import RingOfCovariants
import subprocess

#this assumes that mat has full rank
#turns out this is slow... at least small primes won't work
def KernelVectors(mat):
    mat = mat * mat.denominator()
    exp = 10
    N = 1
    while True:
        exp *= 2
        N = random_prime(2**exp, lbound = 2**(exp - 1))
        print("KernelVectors: choose {}-bit prime number as modulus", exp)
        mat_mod = mat.change_ring(ZZ.quotient(N))
        ker_mod = mat_mod.right_kernel().echelonized_basis_matrix()
        a, b = ker_mod.dimensions()
        if (a, b) != mat.dimensions(): #kernel too large
            continue
        ker = Matrix(QQ, a, b)
        try:
            for i in range(a):
                for j in range(b):
                    ker[i,j] = ker_mod[i,j].rational_reconstruction()
        except ArithmeticError:
            continue
        if mat * ker.transpose() == 0:
            break

    ker = ker * ker.denominator()
    if b - a > 1:
        print("KernelVectors: lattice reduction")
        ker = ker.LLL()
    return ker

def EvaluateCovariants(basis, chi):
    if len(basis) == 0:
        return []

    R = chi.base_ring()
    S = R.cover_ring()
    Rx = PolynomialRing(R, "x")

    print("EvaluateCovariants: computing transvectants...")
    values = EvaluateBasicCovariants(chi, leading_coefficient = False)
    monomials = Set([])
    for b in basis:
        monomials = monomials.union(Set(b.monomials()))
    monomials = [m.degrees() for m in monomials.list()]

    print("EvaluateCovariants: computing powers...")
    powers = [[] for i in range(26)]
    for i in range(26):
        d = 0
        for m in monomials:
            d = max(d, m[i])
        x = R(1)
        for j in range(d + 1):
            powers[i].append(x)
            if j < d:
                x *= values[i]

    print("EvaluateCovariants: substitution in {} monomials...".format(len(monomials)))
    subs_mon = {}
    maxlen = 0
    for m in monomials:
        x = R(1)
        for i in range(26):
            if m[i] > 0:
                x *= powers[i][m[i]]
        subs_mon[m] = x.coefficients(sparse = False)
        subs_mon[m] = [c.lift() for c in subs_mon[m]]
        maxlen = max(maxlen, len(subs_mon[m]))
    #padding in case leading coefficients are zero
    for m in monomials:
        subs_mon[m] = subs_mon[m] + [S(0) for i in range(maxlen + 1 - len(subs_mon[m]))]

    print("EvaluateCovariants: making {} linear combinations...".format(len(basis)))
    res = []
    for b in basis:
        r = []
        mons = [m.degrees() for m in b.monomials()]
        coeffs = b.coefficients()
        for k in range(maxlen + 1):
            c = S(0)
            for i in range(len(mons)):
                c += coeffs[i] * subs_mon[mons[i]][k]
            r.append(R(c))
        res.append(Rx(r))
    return res

class SMF(SageObject):
    r"""
    Constructs Siegel modular forms of weight (k,j) (degree 2)

    sage: SMF(4,0).GetBasis()
    [-Co20^2 + 3*Co40]

    sage: SMF(6,0).GetBasis()
    [-28*Co20^3 + 57*Co20*Co40 + 3*Co60]

    sage: SMF(8,0).GetBasis()
    [Co20^4 - 6*Co20^2*Co40 + 9*Co40^2]

    sage: len(SMF(12,0).GetBasis())
    3
    """
    #prec = 0
    #chi = 0
    #t_chi = 0

    gens = []
    weights = [] #elements of (ZZ,ZZ,ZZ/2ZZ) to account for character
    names = []
    ring = QQ
    gbasis = []
    lt = {}

    def _GetNames(weights):
        names = []
        for i in range(len(weights)):
            j0 = 0
            for j in range(1, len(weights) - i):
                if weights[j] == weights[i]:
                    j0 = j
                else:
                    break
            if j0 == 0:
                names.append("S_{}_{}_{}".format(weight[i][0], weight[i][1], weight[i][2]))
            else:
                assert j0 < 26
                names += ["S_{}_{}_{}{}".format(weight[i][0], weight[i][1], weight[i][2], string.ascii_lowerace[j])
                          for j in range(j0)]

    def _AddGenerators(covariants, weight, character):
        index = 0
        slope = ZZ(weight[1])/ZZ(weight[0])
        for i in range(len(SMF.gens)):
            w = weights[i]
            s = ZZ(w[1])/ZZ(w[0])
            if s > slope or (s == slope and w[0] < weight[0]) or (s == slope and w[0] == weight[0] and w[2] == 0 and character):
                index += 1
            else:
                break
        SMF.gens = SMF.gens[0:index] + covariants + SMF.gens[index:]
        if character:
            eps = GF(2)(1)
        else:
            eps = GF(2)(0)
        SMF.weights = SMF.weights[0:index] + [(weight[0], weight[1], eps) for i in range(len(covariants))] + SMF.weights[index:]
        SMF.names = SMF._GetNames(SMF.weights)
        SMF.ring = PolynomialRing(Rationals(), names)
        newgbasis = []
        for r in SMF.gbasis:
            newr = SMF.ring(0)
            mons = [m.degrees() for m in r.monomials()]
            coeffs = r.coefficients()
            for i in range(len(mons)):
                newr += c[i] * SMF.ring(mons[i][0:index] + [0 for j in range(len(covariants))] + mons[i][index:])
            newgbasis.append(r)
        SMF.gbasis = newgbasis
        newlt = {}
        for d in SMF.lt.keys():
            newlist = []
            for t in SMF.lt[j]:
                newlist.append((t[0:index] + [0 for j in range(len(covariants))] + t[index:]))
            if d < index:
                newlt[d] = newlist
            else:
                newlt[d + len(covariants)] = newlist
        SMF.lt = newlt
        return SMF.ring.gens()[index:index + len(covariants)]

    def _GetGenerators(weight_list, wt, syzygous):
        if wt[0] == 0 and wt[1] == 0 and wt[2] == 0:
            return [[0 for i in range(len(weight_list))]]
        elif wt[0] == 0:
            return []
        elif len(weight_list) == 0:
            return []

        #Compute min_w0, max_w0
        wt0 = weight_list[0]
        max_w0 = min([wt[i] // wt0[i] for i in range(2) if wt0[i] != 0])
        min_w0 = 0
        if wt0[1] > 0:
            slope = ZZ(weight_list[1][1]) / ZZ(weight_list[1][0])
            assert wt0[1] - slope * wt0[0] >= 0
            if wt[1] - slope * wt[0] > 0:
                if wt0[1] - slope * wt0[0] == 0:
                    return []
                else:
                    min_w0 = ceil((wt[1] - slope * wt[0])/(wt0[1] - slope * wt0[0]))

        #adjust max_w0 given the list of syzygous monomials.
        degrees = syzygous.get(index)
        if not degrees is None:
            for d in degrees:
                max_w0 = min(max_w0, d[index] - 1)

        all_ws = []
        for w0 in range(max_w0, min_w0 - 1, -1):
            new_syzygous = {}
            #ignore monomials whose degree in the current covariant is more than w0.
            for n in syzygous:
                if n > index:
                    new_syzygous[n] = [d for d in syzygous[n] if d[index] <= w0]
            ws = SMF._GetGenerators(weight_list[1:], (wt[0]-w0*wt0[0], wt[1]-w0*wt0[1], wt[2] - w0*wt0[2]),
                                    new_syzygous)
            all_ws += [[w0] + w for w in ws]
        return all_ws

    def _CompareMonomials(u, v):
        assert len(u) == len(SMF.gens())
        assert len(u) == len(v)
        for i in range(len(u)):
            if u[i] < v[i]:
                return -1
            elif u[i] > v[i]:
                return 1
        return 0

    def _AddRelation(zerosmf):
        SMF.gbasis.append(zerosmf)
        #find out what the leading term is. Sage doesn't have the monomial order we want...
        d = [m.degrees() for m in zerosmf.monomials()]
        lt = d[0]
        for i in range(1, len(d)):
            if SMF_CompareMonomials(lt, d[i]) == 1:
                lt = d[i]
        #find out where to put it in the dictionary
        index = 0
        r = d[i]
        for j in range(len(r)):
            if r[j] > 0:
                index = j
        if index in SMF.lt:
            SMF.lt[index].append(r)
        else:
            SMF.lt[index] = [r]

    def _ExtractBasis(smfs):
        #expand in terms of covariants
        covariants = []
        for s in smfs:
            assert s.is_monomial()
            w = s.degrees()
            covariants.append(EvaluateMonomialInCovariants(w, SMF.gens))
        #reduce mod Gröbner basis

    def __init__(self, k, j, character = False):
        self.k = k
        self.j = j
        #self.prec = 3
        self.dim = None
        self.basis = None
        self.decomposition = None
        self.fields = None
        self.character = character

    def _EvaluateGens(covariants):
        #this is copy-pasted from EvaluateCovariants (with simplifications)
        if len(SMF.gens) == 0:
            return []

        R = covariants[0].parent()
        monomials = Set([])
        for b in SMF.gens:
            monomials = monomials.union(Set(b.monomials()))
        monomials = [m.degrees() for m in monomials.list()]

        powers = [[] for i in range(26)]
        for i in range(26):
            d = 0
            for m in monomials:
                d = max(d, m[i])
            x = R(1)
            for j in range(d + 1):
                powers[i].append(x)
                if j < d:
                    x *= values[i]

        subs_mon = {}
        for m in monomials:
            x = R(1)
            for i in range(26):
                if m[i] > 0:
                    x *= powers[i][m[i]]
            subs_mon[m] = x

        res = []
        for b in SMF.gens:
            mons = [m.degrees() for m in b.monomials()]
            coeffs = b.coefficients()
            c = R(0)
            for i in range(len(mons)):
                c += coeffs[i] * subs_mon[mons[i]][k]
            res.append(c)
        return res

    def __str__(self):
        s = "Space of Siegel modular form of weight ("+str(self.k)+"," + str(self.j) + ")"
        if self.character:
            s += " with character"
        return s

    def __repr__(self):
        return str(self)

    # def SetBasis(self, L):
    #    CRing = RingOfCovariants(new_ordering = True)
    #    self.basis = [CRing(x) for x in L]

    def Dimension(self):
        if not self.dim is None:
            return self.dim

        if self.j == 0 and self.character:
            self.dim = dim_splitting_SV_All_weight_charac(self.k)['total_dim']
        elif self.j == 0:
            self.dim = dim_splitting_SV_All_weight(self.k)['total_dim']
        elif self.character:
            self.dim = dim_splitting_VV_All_weight_charac(self.k, self.j)['total_dim']
        else:
            self.dim = dim_splitting_VV_All_weight(self.k, self.j)['total_dim']
        return self.dim

    def _KnownSMFs(self):
        if self.dim == 0:
            return []
        else:
            if self.character:
                eps = GF(2)(1)
            else:
                eps = GF(2)(0)
            return SMF._GetGenerators(SMF.weights, (self.k, self.j, eps), SMF.lt)

    # def _subs_chi(basis, chi, t_chi, s_prec):
    #     RingCov = BSC.LCov[0].parent()
    #     basis_expanded = [RingCov(b.subs(BSC.DCov)) for b in basis]
    #     exps = list(chi.dict().keys())
    #     t_chi_vals = list(t_chi.coeffs.values())
    #     R = t_chi_vals[0].parent()
    #     t_chi_comps = [t_chi.coeffs.get(exp, R(0)) for exp in exps]
    #     assert len(t_chi_comps) == 7
    #     gens = list(reduce(lambda x,y:x.union(y), [Set(b.variables()) for b in basis]))
    #     gens_exp = [g.subs(BSC.DCov) for g in gens]
    #     g_exps = [list(g_exp.dict().keys()) for g_exp in gens_exp]
    #     b_exps = list(basis_expanded[0].dict().keys())
    #     vals = list(basis_expanded[0].dict().values())
    #     U = vals[0].parent()
    #     a = U.gens()
    #     g_comps = [[g.dict().get(exp,U(0)) for exp in g_exps[i]] for i,g in enumerate(gens_exp)]
    #     sub_dict = {a[i] : t_chi_comps[i] for i in range(7)}
    #     g_comps_expanded = [[R(g_c.subs(sub_dict)) for g_c in g_comps_s] for g_comps_s in g_comps]
    #     g_c_e = [VectorFJexp([g_exps[l], g_comps_expanded[l]]) for l in range(len(g_exps))]
    #     g_sub_dict = {gens[i] : g_c_e[i] for i in range(len(gens))}
    #     b_comps_exp = [b.subs(g_sub_dict) for b in basis]
    #     #the above line is completely broken when b = 1, so instead, do:
    #     for l in range(len(b_comps_exp)):
    #         if basis[l] == 1:
    #             b_comps_exp[l] = VectorFJexp(chi.parent()(1), s_prec)
    #     return b_comps_exp, b_exps

    # def _create_coeff_matrix(b_comps_exp, b_exps, qexp, i, up_to_val):
    #     Rs = reduce(lambda x,y: x + y,
    #                 [reduce(lambda x,y : x + y,
    #                         [list(b_c.coeffs.values()) for b_c in b_c_e.coeffs.values()])
    #                  for b_c_e in b_comps_exp])[0].parent()
    #     all_vals = []
    #     all_coeffs = []
    #     for b_c_e in b_comps_exp:
    #         b_c = b_c_e.coeffs[b_exps[i]]
    #         mon = b_c.coeffs.get(qexp, Rs(0))
    #         v = mon.valuation()
    #         coeffs = list(mon)
    #         all_vals.append(v)
    #         if (v >= up_to_val):
    #             all_coeffs.append([])
    #         else:
    #             all_coeffs.append(coeffs[:up_to_val-v])
    #     min_val = min(all_vals)
    #     if (min_val < up_to_val):
    #         max_len = max([len(all_coeffs[j]) + all_vals[j] for j in range(len(all_vals)) if all_vals[j] < up_to_val])
    #         for j in range(len(all_vals)):
    #             v = all_vals[j]
    #             if (v >= up_to_val):
    #                 v = max_len
    #             all_coeffs[j] = [0 for l in range(v-min_val)] + all_coeffs[j]
    #     max_len = max([len(a) for a in all_coeffs])
    #     all_coeffs = [a + [0 for j in range(max_len-len(a))] for a in all_coeffs]
    #     mat_coeffs = Matrix(all_coeffs)
    #     return mat_coeffs

    # def _solve_linear_system(V, b_comps_exp, b_exps, up_to_val=0):
    #     ker = V
    #     qexps = reduce(lambda x,y: x.union(y),
    #                    [reduce(lambda x,y: x.union(y),
    #                            [Set(list(b_c.coeffs.keys()))
    #                             for b_c in b_c_e.coeffs.values()])
    #                     for b_c_e in b_comps_exp])
    #     for qexp in qexps:
    #         for i in range(len(b_exps)):
    #             mat_coeffs = SMF._create_coeff_matrix(b_comps_exp, b_exps, qexp, i, up_to_val)
    #             ker_mat = mat_coeffs.kernel()
    #             ker = ker.intersection(ker_mat)
    #     return ker

    # def _GetBasisWithPoles(bsc, prec, taylor_prec, pole_ord, dim):
    #     print("Creating basis of covariants...")
    #     basis = bsc.GetBasis()
    #     print("Done!")
    #     if (len(basis) == 0):
    #         basis = []
    #         return basis, prec, taylor_prec

    #     V = VectorSpace(QQ, len(basis))
    #     ker = V
    #     prec = prec-1
    #     s_prec = taylor_prec-10
    #     print("Attempting to find a basis for covariants in "+str(bsc)+" with pole of order at most "+str(pole_ord))
    #     print("Trying to get to dimension ", dim)
    #     is_first_outer = True
    #     while ((is_first_outer) or (ker.dimension() > dim)):
    #         is_first_outer = False
    #         prec += 1
    #         if (SMF.prec < prec):
    #             print("Recomputing expansion of chi_6_m_2 to precision {}...".format(prec))
    #             SMF.chi = Chi(6,-2).GetFJexp(prec)
    #             SMF.prec = prec
    #             print("Done!")

    #         ker_dim = infinity
    #         is_first = True
    #         while ((is_first) or
    #                ((ker.dimension() > dim) and (ker.dimension() < ker_dim))):
    #             print("Dimension obtained is ", ker.dimension())
    #             is_first = False
    #             ker_dim = ker.dimension()
    #             s_prec += 10
    #             # Compute Taylor expansion: this is cheap.
    #             print("increasing precision in s to {}...".format(s_prec))
    #             t_chi = VectorFJexp(SMF.chi, s_prec)

    #             # Substitution
    #             print("Substituting chi_6_m_2 in basis...")
    #             b_comps_exp, b_exps = SMF._subs_chi(basis, SMF.chi, t_chi, s_prec)
    #             print("Done!")

    #             #Linear algebra
    #             print("Solving linear system...")
    #             ker = SMF._solve_linear_system(V, b_comps_exp, b_exps, up_to_val= -pole_ord)
    #             print("Done!")

    #     # Take only highest valuations
    #     basis = [sum([b.denominator()*b[i]*basis[i] for i in range(len(basis))]) for b in ker.basis()]
    #     return basis, prec, s_prec

    def _ConfirmDimZero(self):
        veck = self.k
        vecj = self.j
        p = 101
        nbp = 5
        for m in range(nbp):
            RingCov = RingOfCovariants(BSC.LW, p = p)
            a = veck + vecj // 2
            vanishing_order = a
            if not self.character:
                basis = BSC(a, vecj).GetBasisWithConditions(p = p)
            else:
                a = 5
                vanishing_order -= 6
                basis = BSC(a, vecj).GetBasis()
                basis = [RingCov(x) for x in basis]
            print("GetBasis: attempting to prove dimension is zero mod p = {}, starting dimension: {}".format(p, len(basis)))

            #proceed as in _GetBasis, but over a finite field
            s_prec = vanishing_order - 1
            q_prec = 2
            current_dim = len(basis)
            prev_dim = current_dim + 1
            chi = Chi(-2, 6).diagonal_expansion(1, 1, p = p)
            R = chi.base_ring().cover_ring()
            q1 = R.gen(0)
            q3 = R.gen(1)
            s = R.gen(2)

            while current_dim > 0 and current_dim < prev_dim: #ensures termination
                chi = Chi(-2, 6).diagonal_expansion(q_prec, s_prec, p = p)
                print("GetBasis: looking for vanishing at order {} along diagonal".format(vanishing_order))
                print("GetBasis: got q-expansion of chi(-2,6) at q-precision {}".format(q_prec))
                qexps = EvaluateCovariants(basis, chi)
                monomials = []
                for i in range(q_prec + 1):
                    for j in range(q_prec + 1):
                        for k in range(s_prec + 1):
                            for l in range(vecj + 1):
                                monomials.append([[i,j,k], l])
                nb = len(monomials)
                mat = Matrix(GF(p), nb, len(basis))
                print("GetBasis: linear algebra over Fp (size {} x {})...".format(nb, len(basis)))
                for j in range(len(basis)):
                    coeffs = qexps[j].coefficients(sparse = False)
                    coeffs = [c.lift() for c in coeffs]
                    coeffs += [R(0) for l in range(vecj + 1 - len(coeffs))]
                    for i in range(nb):
                        e, l = monomials[i]
                        mat[i, j] = coeffs[l].coefficient(e)
                prev_dim = current_dim
                current_dim = len(basis) - mat.rank()
                print ("GetBasis: found dimension {} at q-precision {}".format(current_dim, q_prec))
                q_prec = q_prec + 1

            if current_dim == 0:
                break
            p = next_prime(p)

        return (current_dim == 0)

    def _GetBasis(covbasis, vanishing_order, dim, vecj, keq2 = False):
        # When k == 2 we don't know the dimension is 0, and want to verify it.
        if len(covbasis) == dim:
            return covbasis
        elif not keq2 and (dim == 0):
                return []
        print("GetBasis: starting dimension {}, target {}".format(len(covbasis), dim))

        RingCov = RingOfCovariants(BSC.LW)
        s_prec = vanishing_order - 1
        q_prec = 2
        current_dim = len(covbasis)
        chi = Chi(-2, 6).diagonal_expansion(1, 1)
        R = chi.base_ring().cover_ring()
        q1 = R.gen(0)
        q3 = R.gen(1)
        s = R.gen(2)

        while current_dim > dim:
            chi = Chi(-2, 6).diagonal_expansion(q_prec, s_prec)
            print("GetBasis: looking for vanishing at order {} along diagonal".format(vanishing_order))
            print("GetBasis: got q-expansion of chi(-2,6) at q-precision {}".format(q_prec))
            qexps = EvaluateCovariants(covbasis, chi)
            monomials = []
            for i in range(q_prec + 1):
                for j in range(q_prec + 1):
                    for k in range(s_prec + 1):
                        for l in range(vecj + 1):
                            monomials.append([[i,j,k], l])
            nb = len(monomials)
            mat = Matrix(QQ, nb, len(covbasis))
            print("GetBasis: linear algebra over Fp (size {} x {})...".format(nb, len(covbasis)))
            for j in range(len(covbasis)):
                coeffs = qexps[j].coefficients(sparse = False)
                coeffs = [c.lift() for c in coeffs]
                coeffs += [R(0) for l in range(vecj + 1 - len(coeffs))]
                for i in range(nb):
                    e, l = monomials[i]
                    mat[i, j] = coeffs[l].coefficient(e)
            p = random_prime(1000000, lbound = 500000)
            mat = mat * mat.denominator()
            mat = mat.change_ring(ZZ)
            mat_p = mat.change_ring(GF(p))
            rows = mat_p.pivot_rows()
            current_dim = len(covbasis) - len(rows)
            print ("GetBasis: found dimension {} at q-precision {}".format(current_dim, q_prec))
            mat = Matrix(QQ, [mat.row(i) for i in rows])
            q_prec = ceil(1.3 * q_prec + 1)

        print("GetBasis: linear algebra over QQ (size {} x {}, height {})...".format(mat.nrows(), len(covbasis), mat.height().global_height()))
        ker = mat.right_kernel().basis_matrix()
        ker = ker * ker.denominator()
        ker = ker.change_ring(ZZ)
        print("GetBasis: saturation...")
        ker = ker.saturation()
        if dim > 1:
            print("GetBasis: lattice reduction...")
            ker = ker.LLL()
        res = []
        for v in ker:
            c = RingCov(0)
            for i in range(len(covbasis)):
                c += v[i] * covbasis[i]
            c = c / c.content()
            res.append(c)

        print("GetBasis: done")
        return res

    # def GetBasis(self, prec=3, taylor_prec=20):
    #     if (not self.basis is None and prec <= self.prec):
    #         return self.basis

    #     k = self.k
    #     j = self.j
    #     chi10 = SMF._GetBasisWithPoles(BSC(10,0), prec, taylor_prec, -1, 1)[0][0]
    #     self.basis = []
    #     dim = self.Dimension()

    #     a_max = k + j//2
    #     if (self.character):
    #         a_max -= 5

    #     a_min = a_max % 10
    #     pole_ord = 2 * (a_max // 10)
    #     if (self.character):
    #         pole_ord += 1

    #     a = a_min
    #     while (len(self.basis) < dim):
    #         bsc = BSC(a, j)
    #         self.basis, self.prec, self.s_prec = SMF._GetBasisWithPoles(bsc, prec, taylor_prec, pole_ord, dim)
    #         self.basis = [(chi10)**(pole_ord // 2) * b for b in self.basis]
    #         a += 10
    #         pole_ord -= 2

    #     return self.basis

    def _GetNewGenerators(self, knownsmfs, covbasis, vanishing_order, dim, vecj):
        #Expand knownsmfs as covariants
        knowncovariants = []
        for s in knownsmfs: #a list of monomials
            assert s.is_monomial()
            w = s.degrees()
            knowncovariants.append(EvaluateMonomialInCovariants(w, SMF.gens))

    def _GeneratorsAndRelations(self):
        k = self.k
        j = self.j
        dim = self.Dimension()
        if k != 2 and dim == 0:
            return
        elif k == 2 and dim == 0:
            if self._ConfirmDimZero():
                return

        #get generators from known SMFs
        knownsmfs = self._KnownSMFs()
        knownsmfs = SMF._ExtractBasis(knownsmfs) #this also adds relations
        if len(knownsmfs) == dim:
            return

        #otherwise, construct new generators from covariants
        a = k + j // 2
        vanishing_order = a
        if not self.character:
            covbasis = BSC(a, j).GetBasisWithConditions()
        else:
            a -= 5
            vanishing_order -= 6
            covbasis = BSC(a, j).GetBasis()
        self._GetNewGenerators(knownsmfs, covbasis, vanishing_order, dim, j)

    def GetBasis(self):
        if not self.basis is None:
            return self.basis

        k = self.k
        j = self.j
        self.basis = []
        dim = self.Dimension()
        if (k != 2) and (dim == 0):
            return []
        elif k == 2 and dim == 0:
            if self._ConfirmDimZero():
                return []
            #else, continue with usual algorithm

        a = k + j // 2
        vanishing_order = a
        if not self.character:
            basis = BSC(a, j).GetBasisWithConditions()
        else:
            a -= 5
            vanishing_order -= 6
            basis = BSC(a, j).GetBasis()
        return SMF._GetBasis(basis, vanishing_order, dim, j, (k == 2))

    def WriteBasisToFile(self, filename, mode):
        d = self.Dimension()
        s = "Space of Siegel modular forms of weight ({}, {})".format(self.k, self.j)
        if d == 0:
            return
        if self.character:
            s += " with character\n"
            i = 1
        else:
            s += " without character\n"
            i = 0
        with open(filename, mode) as f:
            if mode == "a":
                f.write("\n\n")
            B = self.GetBasis()
            f.write(s)
            f.write(str(i) + "\n")
            for k in range(d):
                f.write(str(B[k]))
                if k < d - 1:
                    f.write("\n")

    def WriteDecompositionToFile(self, filename, mode):
        if self.Dimension() == 0:
            return
        s = "Eigenform of weight ({}, {})".format(self.k, self.j)
        if self.character:
            s += " with character"
            i = 1
        else:
            s += " without character"
            i = 0
        F = self.HeckeFields()
        D = self.HeckeDecomposition()
        d = len(D)
        with open(filename, mode) as f:
            if mode == "a":
                f.write("\n\n")
            for k in range(d):
                f.write(s + ", number {}\n".format(k + 1))
                f.write(str(i) + "\n")
                f.write(str(F[k].defining_polynomial()))
                f.write("\n")
                e = len(D[k])
                for l in range(e):
                    f.write(str(D[k][l]))
                    if l < e - 1:
                        f.write("\n")
                if k < d - 1:
                    f.write("\n\n")

    # This computes the Hecke action on full basis
    def HeckeAction(self, q, filename="../data/temp", log=True):
        self.WriteBasisToFile(filename + ".in", "w")
        call = ["./hecke_matrices.exe", "{}".format(q), filename + ".in", filename + ".out"]
        run = subprocess.run(call, capture_output=True, check=True)
        subprocess.run(["rm", filename + ".in"])
        if log:
            with open(filename + ".log", "w") as f:
                f.write(run.stdout.decode("ASCII"))

        d = self.Dimension()
        M = Matrix(QQ, d, d)
        with open(filename + ".out", "r") as f:
            for k in range(d):
                line = f.readline().strip("[]\n").split(" ")
                assert len(line) == d, "Line is not of expected length {}".format(d)
                for j in range(d):
                    M[k,j] = QQ(line[j])
        subprocess.run(["rm", filename + ".out"])
        return M

    # This computes a list of Hecke fields as QQ(x)/f_i(x) and lists of
    # covariants over QQ [c^i_0, ..., c_i^{d-1}] such that \sum c^i_k x^k is a
    # Hecke eigenform
    def HeckeDecomposition(self):
        if not self.decomposition is None:
            return self.decomposition
        M = self.HeckeAction(3)
        #print("Matrix of Hecke action at 2:\n{}".format(M))
        fac = M.characteristic_polynomial().factor()
        res = []
        fields = []
        roots = []
        for k in range(len(fac)):
            pol = fac[k][0]
            print("Found eigenvalue with minimal polynomial {}".format(pol))
            if pol.degree() == 1:
                F = QQ
                root = pol.roots()[0][0]
            else:
                R = pol.parent()
                oldpol = pol
                newpol = R(pari.polredbest(pol))
                while (newpol != oldpol):
                    oldpol = newpol
                    newpol = R(pari.polredbest(newpol))
                    print("After one more polredbest:")
                    print(newpol)
                #newpol = R(pari.polredabs(newpol))
                Ry = PolynomialRing(QQ, "y")
                F = NumberField(newpol, "a")
                print("Number field constructed")
                root = F(pari.nfroots(Ry(newpol), pol)[0])
            print("Hecke decomposition: found factor and number field")
            print(pol)
            print(F)
            fields.append(F)
            roots.append(root)
        self.fields = fields

        for k in range(len(self.fields)):
            F = self.fields[k]
            N = Matrix(F, M)
            V = (N - roots[k]).left_kernel().basis()
            assert len(V) == 1, "Should find exactly one eigenvector"
            v = V[0].denominator() * V[0]; #coordinates of v are integers in F.
            #print("Found eigenvector {}".format(v))

            coefficients = []
            g = ZZ(1)
            for l in range(F.degree()):
                if F is QQ:
                    w = v
                else:
                    w = [y.polynomial().padded_list(F.degree())[l] for y in v]
                elt = 0
                for m in range(self.Dimension()):
                    elt += w[m] * self.basis[m]
                coefficients.append(elt)
                g = g.gcd(elt.content())
            for l in range(F.degree()):
                coefficients[l] = coefficients[l]/g
            res.append(coefficients)

        self.decomposition = res
        self.fields = fields
        return res

    def HeckeFields(self):
        if self.decomposition is None:
            self.HeckeDecomposition()
        return self.fields

    def HeckeActionOnEigenvectors(self, q, filename="../data/temp", log=True):
        self.WriteDecompositionToFile(filename + ".in", "w")
        call = ["./hecke_eigenvalues.exe", "{}".format(q), filename + ".in", filename + ".out"]
        if self.character:
            call[1] = "./hecke_eigenvalues_with_character.exe"
        run = subprocess.run(call, capture_output=True, check=True)
        subprocess.run(["rm", filename + ".in"])
        if log:
            with open(filename + ".log", "w") as f:
                f.write(run.stdout.decode("ASCII"))

        res = []
        D = self.HeckeDecomposition()
        with open(filename + ".out", "r") as f:
            for i in range(len(D)):
                d = len(D[i])
                M = Matrix(ZZ, d, d)
                for k in range(d):
                    line = f.readline().strip("[]\n").split(" ")
                    assert len(line) == d, "Line is not of expected length {}".format(d)
                    for j in range(d):
                        M[k,j] = ZZ(line[j])
                res.append(M)
                f.readline()
                f.readline()
        subprocess.run(["rm", filename + ".out"])
        return res

def SMFPrecomputedScalarBasis(k):
    bases = {2: [],
             4: ["-Co20^2 + 3*Co40"],
             6: ["-28*Co20^3 + 57*Co20*Co40 + 3*Co60"],
             8: ["Co20^4 - 6*Co20^2*Co40 + 9*Co40^2"],
             10: ["-160*Co20^5 + 1341*Co20^3*Co40 - 2016*Co20*Co40^2 - 57*Co20^2*Co60 + 36*Co100",
                  "28*Co20^5 - 141*Co20^3*Co40 + 171*Co20*Co40^2 - 3*Co20^2*Co60 + 9*Co40*Co60"],
             12: ["784*Co20^6 - 3192*Co20^4*Co40 + 3249*Co20^2*Co40^2 - 168*Co20^3*Co60 + 342*Co20*Co40*Co60 + 9*Co60^2",
                  "-Co20^6 + 9*Co20^4*Co40 - 27*Co20^2*Co40^2 + 27*Co40^3",
                  "96*Co20^6 - 305*Co20^4*Co40 + 240*Co20^2*Co40^2 - 35*Co20^3*Co60 + 48*Co20*Co40*Co60 + 12*Co20*Co100"],
             14: ["160*Co20^7 - 1821*Co20^5*Co40 + 6039*Co20^3*Co40^2 + 57*Co20^4*Co60 - 6048*Co20*Co40^3 - 171*Co20^2*Co40*Co60 - 36*Co20^2*Co100 + 108*Co40*Co100",
                  "-28*Co20^7 + 225*Co20^5*Co40 - 594*Co20^3*Co40^2 + 3*Co20^4*Co60 + 513*Co20*Co40^3 - 18*Co20^2*Co40*Co60 + 27*Co40^2*Co60"],
             16: ["9952*Co20^8 - 80469*Co20^6*Co40 + 198720*Co20^4*Co40^2 - 879*Co20^5*Co60 - 155952*Co20^2*Co40^3 + 9495*Co20^3*Co40*Co60 - 14256*Co20*Co40^2*Co60 - 171*Co20^2*Co60^2 - 324*Co20^3*Co100 + 108*Co60*Co100",
                  "-784*Co20^8 + 5544*Co20^6*Co40 - 12825*Co20^4*Co40^2 + 168*Co20^5*Co60 + 9747*Co20^2*Co40^3 - 846*Co20^3*Co40*Co60 + 1026*Co20*Co40^2*Co60 - 9*Co20^2*Co60^2 + 27*Co40*Co60^2",
                  "Co20^8 - 12*Co20^6*Co40 + 54*Co20^4*Co40^2 - 108*Co20^2*Co40^3 + 81*Co40^4",
                  "-96*Co20^8 + 593*Co20^6*Co40 - 1155*Co20^4*Co40^2 + 35*Co20^5*Co60 + 720*Co20^2*Co40^3 - 153*Co20^3*Co40*Co60 + 144*Co20*Co40^2*Co60 - 12*Co20^3*Co100 + 36*Co20*Co40*Co100"],
             18: ["-21952*Co20^9 + 134064*Co20^7*Co40 - 272916*Co20^5*Co40^2 + 7056*Co20^6*Co60 + 185193*Co20^3*Co40^3 - 28728*Co20^4*Co40*Co60 + 29241*Co20^2*Co40^2*Co60 - 756*Co20^3*Co60^2 + 1539*Co20*Co40*Co60^2 + 27*Co60^3",
                  "-160*Co20^9 + 2301*Co20^7*Co40 - 11502*Co20^5*Co40^2 - 57*Co20^6*Co60 + 24165*Co20^3*Co40^3 + 342*Co20^4*Co40*Co60 - 18144*Co20*Co40^4 - 513*Co20^2*Co40^2*Co60 + 36*Co20^4*Co100 - 216*Co20^2*Co40*Co100 + 324*Co40^2*Co100",
                  "28*Co20^9 - 309*Co20^7*Co40 + 1269*Co20^5*Co40^2 - 3*Co20^6*Co60 - 2295*Co20^3*Co40^3 + 27*Co20^4*Co40*Co60 + 1539*Co20*Co40^4 - 81*Co20^2*Co40^2*Co60 + 81*Co40^3*Co60",
                  "-2688*Co20^9 + 14012*Co20^7*Co40 - 24105*Co20^5*Co40^2 + 1268*Co20^6*Co60 + 13680*Co20^3*Co40^3 - 4254*Co20^4*Co40*Co60 + 3456*Co20^2*Co40^2*Co60 - 105*Co20^3*Co60^2 - 336*Co20^4*Co100 + 144*Co20*Co40*Co60^2 + 684*Co20^2*Co40*Co100 + 36*Co20*Co60*Co100"]}
    if k in bases.keys():
        return bases[k]
    else:
        return None

#polredabs is running into problems when k is too large...
def WriteAllSpaces(kbound = 20, jbound = 16, dimbound = 6, filename = "../data/all.in"):
    mode = "w"
    for j in range(0, jbound + 1, 2):
        for k in range(kbound + 1):
            if k == 0 and j == 0:
                continue
            for char in [False, True]:
                print("\nDoing SMF({}, {}, character = {})".format(k, j, char))
                S = SMF(k, j, character = char)
                d = S.Dimension()
                if d > 0 and d <= dimbound:
                    S.GetBasis()
                    print("Basis done")
                    S.WriteDecompositionToFile(filename, mode);
                    mode = "a"

def WritePrimes(bound = 200, filename = "../data/primes.in"):
    with open(filename, "w") as f:
        for j in range(bound, 1, -1):
            if ZZ(j).is_prime():
                f.write(str(j))
                f.write("\n")
                if j*j <= bound:
                    f.write(str(j*j))
                    f.write("\n")
