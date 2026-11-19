"""
This file contains functions to compute a basis for spaces of Siegel modular
forms S_{k,j}(Gamma(1)), with or without character
"""

import string
import subprocess

from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.all import NumberField, pari, next_prime, Infinity
from sage.functions.other import ceil, floor
from sage.sets.set import Set

from BinarySexticsCovariants import BinarySexticsCovariants as BSC
from BinarySexticsCovariants import EvaluateBasicCovariants, RingOfCovariants, EvaluateMonomial, RandomSextic
from ThetaFourier import Chi
from ModuleGenerators import BoundOnModuleGenerators
from DimFormulaSMFScalarValuedLevel1WithoutCharacter import dim_splitting_SV_All_weight
from DimFormulaSMFVectorValuedLevel1WithoutCharacter import dim_splitting_VV_All_weight
from DimFormulaSMFScalarValuedLevel1WithCharacter import dim_splitting_SV_All_weight_charac
from DimFormulaSMFVectorValuedLevel1WithCharacter import dim_splitting_VV_All_weight_charac

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

    gens = []
    weights = [] #elements of (ZZ,ZZ,ZZ/2ZZ) to account for character
    slope_ordering = []
    slopes = []
    names = []
    ring = QQ
    gbasis = []
    lt = {}
    jmax = -2
    chi10cov = BSC(10,0).GetBasisWithConditions(cusp = True)[0]
    basic_data = []

    def _GetNames(weights):
        names = []
        i = 0
        while i < len(weights):
            w = weights[i]
            j0 = 0
            for j in range(1, len(weights) - i):
                if weights[i + j] == w:
                    j0 = j
                else:
                    break
            if j0 == 0:
                names.append("S_{}_{}_{}".format(*w))
            else:
                assert j0 < 26
                names += ["S_{}_{}_{}{}".format(*w, string.ascii_lowercase[j])
                          for j in range(j0 + 1)]
            i = i + j0 + 1
        return names

    def _AddGenerators(covariants, weight): #weight contains character
        print("Adding {} generators of weight {}".format(len(covariants), weight))
        SMF.gens += covariants
        SMF.weights += [weight for i in range(len(covariants))]
        SMF.names = SMF._GetNames(SMF.weights)
        SMF.ring = PolynomialRing(QQ, len(SMF.names), SMF.names, order = "neglex")
        newgbasis = []
        for r in SMF.gbasis:
            newr = SMF.ring(0)
            mons = [list(m.degrees()) for m in r.monomials()]
            coeffs = r.coefficients()
            for i in range(len(mons)):
                newr += coeffs[i] * SMF.ring.monomial(*(mons[i] + [0 for j in range(len(covariants))]))
            newgbasis.append(newr)
        SMF.gbasis = newgbasis
        SMF.slopes = [QQ(w[1]) / QQ(w[0]) for w in SMF.weights]
        SMF.slope_ordering = [i for i in range(len(SMF.weights))]
        SMF.slope_ordering.sort(key = lambda i: SMF.slopes[i], reverse = True)
        SMF.lt = {}
        for j in range(len(SMF.weights)):
            SMF.lt[j] = []
        for g in SMF.gbasis:
            d = g.lm().degrees()
            d = [d[i] for i in SMF.slope_ordering]
            index = -1
            for i in range(len(d) - 1, -1, -1):
                if d[i] > 0:
                    index = i
                    break
            SMF.lt[index].append(d)

        return list(SMF.ring.gens())[-len(covariants):]

    def _AddRelation(zerosmf):
        SMF.gbasis.append(zerosmf)
        d = zerosmf.lm().degrees()
        d = [d[i] for i in SMF.slope_ordering]
        #find out where to put it in the dictionary
        index = -1
        for j in range(len(d) - 1, -1, -1):
            if d[j] > 0:
                index = j
                break
        SMF.lt[index].append(d)

    def _GetGeneratorsRec(weight_list, index, wt, syzygous):
        if wt[0] == 0 and wt[1] == 0 and wt[2] == 0:
            return [[0 for i in range(len(weight_list))]]
        elif len(weight_list) == 0:
            return []
        elif wt[1] > SMF.slopes[SMF.slope_ordering[index]] * wt[0]:
            return []

        #Compute min_w0, max_w0; do not use slope, so min_w0=0
        wt0 = weight_list[0]
        max_w0 = min([wt[i] // wt0[i] for i in range(2) if wt0[i] != 0])
        min_w0 = 0

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
            ws = SMF._GetGeneratorsRec(weight_list[1:], index + 1,
                                       (wt[0]-w0*wt0[0], wt[1]-w0*wt0[1], wt[2] - w0*wt0[2]),
                                       new_syzygous)
            all_ws += [[w0] + w for w in ws]

        return all_ws

    def _GetGenerators(wt, target_dim, new_generators = True):
        print("GetGenerators: enumerating monomials (target {})...".format(target_dim));
        weight_list = [SMF.weights[j] for j in SMF.slope_ordering]
        all_ws_slope_ordering = SMF._GetGeneratorsRec(weight_list, 0, wt, SMF.lt)
        all_ws = []
        for w in all_ws_slope_ordering:
            new_w = [0 for i in range(len(w))]
            for i in range(len(w)):
                new_w[SMF.slope_ordering[i]] = w[i]
            all_ws.append(new_w)
        monomials = [SMF.ring.monomial(*w) for w in all_ws]
        monomials.sort(reverse = True) #leading monomials first
        print("GetGenerators: found {} monomials".format(len(monomials)))

        if (not new_generators) and len(monomials) == target_dim:
            return monomials, [], 0

        covs = []
        chi10_exp = []
        for m in monomials:
            d = m.degrees()
            n = 0 #exponent of chi5
            for i in range(len(d)):
                if SMF.weights[i][2] == 1:
                    n += d[i]
            assert n % 2 == wt[2]
            cov = EvaluateMonomial(d, SMF.gens)
            cov *= SMF.chi10cov ** (n // 2)
            covs.append(cov)
            chi10_exp.append(n // 2)

        if not new_generators:
            assert len(monomials) > target_dim
            #use evaluations to find linear dependencies.
            rank = 0
            eval_data = []
            R = PolynomialRing(QQ, ["x", "y"])
            #Collect powers of chi10
            index = 0
            while rank < target_dim:
                print("GetGenerators: evaluation data...")
                for i in range(target_dim - rank + 10):
                    if index < len(SMF.basic_data):
                        basic = SMF.basic_data[index]
                    else:
                        f = RandomSextic(R, 10)
                        basic = EvaluateBasicCovariants(f)
                        SMF.basic_data.append(basic)
                    index += 1
                    subs_dict = {}
                    for j in range(26):
                        subs_dict[BSC.ring.gen(j)] = basic[j]
                    chi10 = QQ(SMF.chi10cov.subs(subs_dict))
                    smf_values = [QQ(pol.subs(subs_dict)) for pol in SMF.gens]
                    eval_line = [EvaluateMonomial(monomials[j].degrees(), smf_values) * chi10**chi10_exp[j]
                                 for j in range(len(monomials))]
                    eval_data.append(eval_line)
                mat = Matrix(QQ, eval_data).transpose() #lines are monomials
                print("GetGenerators: linear algebra...");
                rels = mat.left_kernel().echelonized_basis()
                rank = len(monomials) - len(rels)

            assert rank == target_dim

        else:
            print("GetGenerators: reduction...");
            reductions = [BSC.Reduce(c) for c in covs]

            #linear algebra to make sure we output a linearly independent family (add relations)
            V = Set()
            for r in reductions:
                V = V.union(Set(r.monomials()))
            V = V.list()
            mat = Matrix(QQ, len(monomials), len(V))
            for i in range(len(monomials)):
                for j in range(len(V)):
                    mat[i,j] = reductions[i].coefficient(V[j])
            #kernel of mat gives relations; pivot rows give linearly independent family
            print("GetGenerators: linear algebra...");
            rels = mat.left_kernel().echelonized_basis()

        nb_rel = len(rels)
        remove = []
        lm = []
        for rel in rels:
            rel = rel * rel.denominator()
            rel = rel.list()
            pol = SMF.ring(0)
            for i in range(len(rel)):
                pol += rel[i] * monomials[i]
            SMF._AddRelation(pol)
            lm.append(pol.lm())
            remove.append(monomials.index(pol.lm()))
        print("GetGenerators: added {} new relations with leading monomials {}".format(len(lm), lm))

        if new_generators:
            reductions = [reductions[j] for j in range(len(monomials)) if not j in remove]
        else:
            reductions = []
        monomials = [monomials[j] for j in range(len(monomials)) if not j in remove]

        return monomials, reductions, nb_rel

    def _DiagonalExpansion(basis, chi):
        if len(basis) == 0:
            return []

        R = chi.base_ring()
        S = R.cover_ring()
        Rx = PolynomialRing(R, "x")

        print("DiagonalExpansion: computing transvectants...")
        values = EvaluateBasicCovariants(chi, leading_coefficient = False)
        monomials = Set([])
        for b in basis:
            monomials = monomials.union(Set(b.monomials()))
        monomials = [m.degrees() for m in monomials.list()]

        print("DiagonalExpansion: computing powers...")
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

        print("DiagonalExpansion: substitution in {} monomials...".format(len(monomials)))
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

        print("DiagonalExpansion: making {} linear combinations...".format(len(basis)))
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

    def __init__(self, k, j, character = False):
        self.k = k
        self.j = j
        #self.prec = 3
        self.dim = None
        self.basis = None
        self.decomposition = None
        self.fields = None
        self.character = character

    def __str__(self):
        s = "Space of Siegel modular form of weight ("+str(self.k)+"," + str(self.j) + ")"
        if self.character:
            s += " with character"
        return s

    def __repr__(self):
        return str(self)

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
                a -= 5
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
                qexps = SMF._DiagonalExpansion(basis, chi)
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

    #return list of SMFs, list of covariants, nb of new generators, nb of new relations
    def _AddGeneratorsAndRelations(self, new_generators = True):
        dim = self.Dimension()
        if self.k != 2 and dim == 0:
            return [], [], 0, 0
        elif self.k == 2 and dim == 0:
            if self._ConfirmDimZero():
                return [], [], 0, 0

        #get generators from known SMFs
        wt = (self.k, self.j, GF(2)(0))
        if self.character:
            wt = (self.k, self.j, GF(2)(1))
        knownsmfs, knowncovs, nb_rel = SMF._GetGenerators(wt, dim, new_generators = new_generators)
        if len(knownsmfs) == dim:
            return knownsmfs, knowncovs, 0, nb_rel
        assert new_generators

        #otherwise, construct new generators from covariants
        a = self.k + self.j // 2
        vanishing_order = a
        if not self.character:
            covbasis = BSC(a, self.j).GetBasisWithConditions()
            all_monomials = BSC(a, self.j).GetBasis()
        else:
            a -= 5
            vanishing_order -= 6
            covbasis = BSC(a, self.j).GetBasis()
            all_monomials = covbasis

        #get supplementary vector space to knowncovs
        if len(knownsmfs) > 0:
            mat = Matrix(QQ, [[c.coefficient(m) for m in all_monomials] for c in knowncovs + covbasis])
            covbasis = [covbasis[i - len(knowncovs)] for i in mat.pivot_rows()[len(knowncovs):]]
            dim = dim - len(knownsmfs)

        if len(covbasis) == dim:
            new_gens = covbasis
        else: #do linear algebra.
            s_prec = vanishing_order - 1
            q_prec = 2
            current_dim = len(covbasis)
            chi = Chi(-2, 6).diagonal_expansion(1, 1)
            R = chi.base_ring().cover_ring()
            q1 = R.gen(0)
            q3 = R.gen(1)
            s = R.gen(2)
            p = 101

            while current_dim > dim:
                chi = Chi(-2, 6).diagonal_expansion(q_prec, s_prec)
                print("GetBasis: looking for vanishing at order {} along diagonal".format(vanishing_order))
                print("GetBasis: got q-expansion of chi(-2,6) at q-precision {}".format(q_prec))

                qexps = SMF._DiagonalExpansion(covbasis, chi)
                monomials = []
                for i in range(q_prec + 1):
                    for j in range(q_prec + 1):
                        for k in range(s_prec + 1):
                            for l in range(self.j + 1):
                                monomials.append([[i,j,k], l])
                nb = len(monomials)
                mat = Matrix(QQ, nb, len(covbasis))
                print("GetBasis: linear algebra over Fp (size {} x {})...".format(nb, len(covbasis)))
                for j in range(len(covbasis)):
                    coeffs = qexps[j].coefficients(sparse = False)
                    coeffs = [c.lift() for c in coeffs]
                    coeffs += [R(0) for l in range(self.j + 1 - len(coeffs))]
                    for i in range(nb):
                        e, l = monomials[i]
                        mat[i, j] = coeffs[l].coefficient(e)
                mat = mat * mat.denominator()
                mat = mat.change_ring(ZZ)
                mat_p = mat.change_ring(GF(p))
                current_dim = len(covbasis) - mat_p.rank()
                print ("GetBasis: found dimension {} at q-precision {}".format(current_dim, q_prec))
                q_prec += 1
                p = next_prime(p)

            assert current_dim == dim
            print("GetBasis: linear algebra over QQ (size {} x {}, height {})...".format(mat.nrows(), len(covbasis), mat.height().global_height()))
            ker = mat.right_kernel().basis_matrix()
            ker = ker * ker.denominator()
            ker = ker.change_ring(ZZ)
            print("GetBasis: saturation...")
            ker = ker.saturation()
            if dim > 1:
                print("GetBasis: lattice reduction...")
                ker = ker.LLL()

            new_gens = []
            for v in ker:
                c = BSC.ring(0)
                for i in range(len(covbasis)):
                    c += v[i] * covbasis[i]
                new_gens.append(c)

        new_smfs = SMF._AddGenerators(new_gens, wt)
        return knownsmfs + new_smfs, knowncovs + new_gens, len(new_gens), nb_rel

    def _AllGeneratorsAndRelations(j, bound = 40):
        assert SMF.jmax == j - 2
        check = 0
        k = 2
        kmax = BoundOnModuleGenerators(j)
        while check < bound or k <= kmax:
            print("\nAllGeneratorsAndRelations: j = {}, k = {}, no character".format(j, k))
            _, _, n1, m1 = SMF(k, j, character = False)._AddGeneratorsAndRelations(new_generators = (k <= kmax))
            print("\nAllGeneratorsAndRelations: j = {}, k = {}, with character".format(j, k))
            _, _, n2, m2 = SMF(k, j, character = True)._AddGeneratorsAndRelations(new_generators = (k <= kmax))
            if n1 == 0 and n2 == 0:
                check += 1
            else:
                check = 0
            k += 1
        SMF.jmax = j

    def GetBasis(self, use_ring = True):
        if use_ring:
            for j in range(SMF.jmax + 2, self.j + 2, 2):
                SMF._AllGeneratorsAndRelations(j)
        res = self._AddGeneratorsAndRelations()
        # the covariants of the basis, for HeckeDecomposition; hecke_matrices.exe needs
        # integral coefficients
        self.basis = [c * c.denominator() for c in res[1]]
        return res

    def ReadGenerators(prefix = "SMF_"):
        names = []
        with open(prefix + "names.dat") as f:
            for line in f:
                names.append(line.strip("\n"))
        SMF.names = names
        SMF.ring = PolynomialRing(QQ, len(SMF.names), SMF.names, order = "neglex")
        weights = []
        SMF.jmax = 0
        for n in names:
            _, k, j, eps = n.split("_")
            weights.append((ZZ(k), ZZ(j), GF(2)(eps[0])))
            SMF.jmax = max(SMF.jmax, ZZ(j))
        SMF.weights = weights
        SMF.slopes = [QQ(w[1]) / QQ(w[0]) for w in weights]
        SMF.slope_ordering = [i for i in range(len(weights))]
        SMF.slope_ordering.sort(key = lambda i: SMF.slopes[i], reverse = True)

        gens = []
        with open(prefix + "gens.dat") as f:
            for line in f:
                gens.append(BSC.ring(line))
        SMF.gens = gens

        gbasis = []
        with open(prefix + "rels.dat") as f:
            for line in f:
                gbasis.append(SMF.ring(line))
        SMF.gbasis = gbasis
        SMF.lt = {}
        for j in range(len(weights)):
            SMF.lt[j] = []
        for x in gbasis:
            d = x.lm().degrees()
            d = [d[i] for i in SMF.slope_ordering]
            index = -1
            for i in range(len(d) - 1, -1, -1):
                if d[i] > 0:
                    index = i
                    break
            SMF.lt[index].append(d)

    def PrintGenerators(prefix = "SMF_"):
        with open(prefix + "gens.dat", "w") as f:
            for x in SMF.gens:
                f.write(str(x))
                f.write("\n")
        with open(prefix + "rels.dat", "w") as f:
            for x in SMF.gbasis:
                f.write(str(x))
                f.write("\n")
        with open(prefix + "names.dat", "w") as f:
            for x in SMF.names:
                f.write(x)
                f.write("\n")

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
            self.GetBasis()
            B = self.basis
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
