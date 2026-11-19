"""
This file contains functions to compute a basis for the space of covariants of binary sextics C_{a,b} of degree a and order b.
"""

## imports
from sage.structure.sage_object import SageObject
from sage.all import Matrix, Partitions, ZZ, QQ, PolynomialRing, random_prime, ceil, TermOrder
from sage.combinat.q_analogues import q_binomial
from sage.misc.prandom import randint
from sage.rings.invariants.invariant_theory import AlgebraicForm, transvectant
from sage.arith.misc import next_prime
from sage.rings.finite_rings.finite_field_constructor import GF

def ListOfWeights(new_ordering = False):
    if new_ordering:
        return [(2, 0), (4, 0), (6, 0), (10, 0), (15, 0), (3, 2), (5, 2), (7, 2),
                (8, 2), (10, 2), (12, 2), (2, 4), (4, 4), (5, 4), (7, 4), (9, 4),
                (1, 6), (3, 6), (4, 6), (6, 6), (6, 6), (2, 8), (3, 8), (5, 8),
                (4, 10), (3, 12)]
       # return [(1, 6), (2, 8), (3, 12), (3, 8), (4, 10), (2, 4), (3, 6), (5, 8),
       #         (4, 6), (4, 4), (6, 6), (6, 6), (5, 4), (3, 2), (7, 4), (9, 4),
       #         (5, 2), (7, 2), (8, 2), (10, 2), (12, 2), (2, 0), (4, 0),
       #         (6, 0), (10, 0), (15, 0)]
    else:
        return [(1, 6), (2, 0), (2, 4), (2, 8), (3, 2), (3, 6), (3, 8), (3, 12),
                (4, 0), (4, 4), (4, 6), (4, 10), (5, 2), (5, 4), (5, 8), (6, 0),
                (6, 6), (6, 6), (7, 2), (7, 4), (8, 2), (9, 4), (10, 0), (10, 2),
                (12, 2), (15, 0)]

def RingOfCovariants(LW, p = 0):
    cov_names = []
    i = 1
    for k in LW:
        name = "Co{}{}".format(k[0], k[1])
        if k == (6, 6):
            name += str(i)
            i += 1
        cov_names.append(name)
    if p == 0:
        base_ring = QQ
    else:
        base_ring = GF(p)
    return PolynomialRing(base_ring, cov_names,
                          #order = TermOrder('wdegrevlex', tuple([w[0] for w in LW]))
                          order = TermOrder('neglex')
                          )

# Only leading coefficients by default, otherwise all coefficients
def EvaluateBasicCovariants(sextic, leading_coefficient = True):
    LW = BinarySexticsCovariants.LW
    R = sextic.base_ring()
    Rx = PolynomialRing(R, "x")
    C = {}
    f = AlgebraicForm(2, 6, sextic, *sextic.parent().gens()[:2])
    cofactors = {(1,6): 1, (2,0): 60, (2,4): 75, (2,8): 90, (3,2): 2250,
                 (3,6): 2250, (3,8): 450, (3,12): 540, (4,0): 11250, (4,4): 67500,
                 (4,6): 13500, (4,10): 13500, (5,2): 168750, (5,4): 67500,
                 (5,8): 405000, (6,0): 10125000, (6,6): 2025000, (6,6,2): 2700000,
                 (7,2): 151875000, (7,4): 60750000, (8,2): 15187500, (9,4): 9112500000,
                 (10,0): 227812500000, (10,2): 13668750000,
                 (12,2): 8201250000000, (15,0): 384433593750}

    if sextic == 0:
        if leading_coefficient:
            return [R(0) for i in range(26)]
        else:
            return [Rx(0) for i in range(26)]
    C[(1,6)] = f
    C[(2,0)] = transvectant(f, f, 6)
    C[(2,4)] = transvectant(f, f, 4)
    C[(2,8)] = transvectant(f, f, 2)
    C[(3,2)] = transvectant(f, C[(2,4)], 4)
    C[(3,6)] = transvectant(f, C[(2,4)], 2)
    C[(3,8)] = transvectant(f, C[(2,4)], 1)
    C[(3,12)] = transvectant(f, C[(2,8)], 1)
    C[(4,0)] = transvectant(C[(2,4)], C[(2,4)], 4)
    C[(4,4)] = transvectant(f, C[(3,2)], 2)
    C[(4,6)] = transvectant(f, C[(3,2)], 1)
    C[(4,10)] = transvectant(C[(2,8)], C[(2,4)], 1)
    C[(5,2)] = transvectant(C[(2,4)], C[(3,2)], 2)
    C[(5,4)] = transvectant(C[(2,4)], C[(3,2)], 1)
    C[(5,8)] = transvectant(C[(2,8)], C[(3,2)], 1)
    C[(6,0)] = transvectant(C[(3,2)], C[(3,2)], 2)
    C[(6,6)] = transvectant(C[(3,6)], C[(3,2)], 1)
    C[(6,6,2)] = transvectant(C[(3,8)], C[(3,2)], 2)
    C32_2 = transvectant(C[(3,2)],C[(3,2)],0)
    C[(7,2)] = transvectant(f, C32_2, 4)
    C[(7,4)] = transvectant(f, C32_2, 3)
    C[(8,2)] = transvectant(C[(2,4)], C32_2, 3)
    C[(9,4)] = transvectant(C[(3,8)], C32_2, 4)
    C32_3 = transvectant(C[(3,2)],C32_2,0)
    C[(10,0)] = transvectant(f, C32_3, 6)
    C[(10,2)] = transvectant(f, C32_3, 5)
    C[(12,2)] = transvectant(C[(3,8)], C32_3, 6)
    C32_4 = transvectant(C32_2,C32_2,0)
    C[(15,0)] = transvectant(C[(3,8)], C32_4, 8)

    #could be more efficient if we only want leading coefficient
    if leading_coefficient:
        for k in C.keys():
            C[k] = cofactors[k] * R(C[k].polynomial().coefficient([k[1], 0]))
    else:
        for k in C.keys():
            pol = C[k].polynomial()
            coeffs = [pol.coefficient([i, k[1] - i]) for i in range(k[1] + 1)]
            C[k] = cofactors[k] * Rx(coeffs)

    res = [C[wt] for wt in LW]
    res[LW.index((6,6)) + 1] = C[(6,6,2)]
    return res

def EvaluateMonomial(wt, values):
    R = values[0].parent()
    res = R(1)
    for i in range(len(wt)):
        if wt[i] > 0:
            res *= values[i] ** wt[i]
    return res

def EvaluateMonomials(wts, values_list):
    nb = len(values_list)
    if nb == 0:
        return []
    R = values_list[0][0].parent()
    k = len(values_list[0])
    degrees = [0 for i in range(k)]
    for i in range(k):
        #find out the largest degree of R.gens()[i] appearing in wts.
        for w in wts:
            degrees[i] = max(degrees[i], w[i])
    res = []
    for values in values_list:
        powers = [[] for i in range(k)]
        #compute powers
        for i in range(k):
            x = R(1)
            for j in range(degrees[i] + 1):
                powers[i].append(x)
                if j < degrees[i]:
                    x *= values[i]
        #compute monomials
        ev = [R(1) for w in wts]
        for j in range(len(wts)):
            for i in range(k):
                if wts[j][i] > 0:
                    ev[j] *= powers[i][wts[j][i]]
        res.append(ev)
    return res

def RandomSextic(R, bound, zeroa5a6 = False):
    x = R.gens()[0]
    y = R.gens()[1]
    f = R(0)
    start = 0
    if zeroa5a6:
        start = 2
    for i in range(start, 7):
        f += randint(-bound, bound + 1) * x ** i * y ** (6-i)
    return f

def RandomSL2(bound):
    g = 2
    while not g == 1:
        a = randint(-bound, bound)
        b = randint(-bound, bound)
        g, u, v = ZZ(a).xgcd(b)
    return Matrix([[a, b],[-v, u]])

def QuarticTransform(f, mat):
    R = f.parent()
    a = mat[0,0]
    b = mat[0,1]
    c = mat[1,0]
    d = mat[1,1]
    x = R.gen(0)
    y = R.gen(1)
    q = f // x**2
    q = q.subs({x: a*x + c*y, y: b*x + d*y})
    return x**2 * q

# we use a class in order to perform initialization only once

class BinarySexticsCovariants(SageObject):

    r"""
     Constructs spaces of covariants of binary sextics

     EXAMPLES:

     This example is Example 2.1 in the overleaf. :

        sage: bsc = BinarySexticsCovariants(6,0)
        sage: bsc.GetBasisAndRelations()
        ([Co60, Co20*Co40, Co20^3], [])

    """

    LW = ListOfWeights(new_ordering = True)
    ring = RingOfCovariants(LW)
    LCo = ring.gens()

    #Stroh's variables are (up to scaling, with old and new ordering):
    #0     3    2    1    7     6    5    4    11    10   9     8    14   13
    #0     1    5    21   2     3    6    13   4     8    9     22   7    12
    #f     H    i    A    T     q    p    l    r     s    Delta B    t    u
    #Co16  Co28 Co24 Co20 Co312 Co38 Co36 Co32 Co410 Co46 Co44  Co40 Co58 Co54
    #12   16    17    15   19   18   20   21   23    22    24     25
    #16   10    11    23   14   17   18   15   19    24    20     25
    #m    v     w     C    pi   n    nu   rho  mu    D     lambda R
    #Co52 Co661 Co662 Co60 Co74 Co72 Co82 Co94 Co102 Co100 Co122  Co150

    # Stroh's relations are in weights:
    # S1     S2     S3     S4     S5     S6     S7     S8     S9    S10    S11
    # (6,24) (6,20) (5,16) (5,18) (6,16) (6,12) (6,14) (6,10) (6,8) (7,12) (7,12)
    # S12   S13    S14   S15   S16     S17    S18   S19    S20
    # (7,6) (8,10) (8,8) (9,8) (10,10) (11,8) (9,6) (13,8) (16,6)

    #We index the elements of SyzygousMonomials by the largest j such that LCo[j]
    #appears in the monomial.
    Co16 = LCo[0]
    Co28 = LCo[1]
    Co312 = LCo[2]
    Co38 = LCo[3]
    Co410 = LCo[4]
    Co24 = LCo[5]
    Co36 = LCo[6]
    Co58 = LCo[7]
    Co46 = LCo[8]
    Co44 = LCo[9]
    Co661 = LCo[10]
    Co662 = LCo[11]
    Co54 = LCo[12]
    Co32 = LCo[13]
    Co74 = LCo[14]
    Co94 = LCo[15]
    Co52 = LCo[16]
    Co72 = LCo[17]
    Co82 = LCo[18]
    Co102 = LCo[19]
    Co122 = LCo[20]
    Co20 = LCo[21]
    Co40 = LCo[22]
    Co60 = LCo[23]
    Co100 = LCo[24]
    Co150 = LCo[25]

    # After computations using _ComputeBasisAndRelations, we found:
    SyzygousMonomials = {}
    gbasis = []

    def __init__(self, a, b):
        self.a = a
        self.b = b
        self.weight = (a,b)

    def __str__(self):
        return "Space of covariants of binary sextics of degree " + str(self.a) + " and order " + str(self.b)

    def __repr__(self):
        return str(self)

    def Dimension2(self):
        # using the Cayley-Sylvester formula
        a = self.a
        b = self.b
        n = 3 * a - b // 2
        def p(k,n):
            return Partitions(n,max_length=k, max_part=6).cardinality()
        return p(a,n) - p(a,n-1)

    def Dimension(self):
        a = self.a
        b = self.b
        if ((b % 2) == 1):
            return 0
        else:
            R = PolynomialRing(ZZ, ['p'])
            p = R.gen()
            n = 3*a-b//2
            if (n < 0):
                return 0
            f = (1-p)*q_binomial(6+a,a,p)
            d = f.list()[n]
            return d

    #this outputs the leading monomials first wrt the chosen ordering
    def _GetGeneratorsCov(weight_list, wt, syzygous = None, use_syzygous = True):
        if use_syzygous:
            if syzygous is None:
                syzygous = {}
                for n in BinarySexticsCovariants.SyzygousMonomials.keys():
                    syzygous[n] = [m.degrees() for m in BinarySexticsCovariants.SyzygousMonomials[n]]
        else:
            syzygous = {}
        index = 26 - len(weight_list)

        #Early abort cases
        if wt[0] < 0 or wt[1] < 0 or wt[1] > 6 * wt[0]:
            return []
        elif wt[0] == 0 and wt[1] == 0:
            return [[0 for i in range(len(weight_list))]]
        elif wt[0] == 0:
            return []
        elif len(weight_list) == 0:
            return []
        #elif len(weight_list) <= 5 and wt[1] > 0: #no vector-valued covariants left
        #    return []
        #elif len(weight_list) <= 8 and wt[0] % 2 == 1 and wt[0] < 15: #only R has an odd a
        #    return []

        #Compute min_w0, max_w0
        wt0 = weight_list[0]
        max_w0 = min([wt[i] // wt0[i] for i in range(2) if wt0[i] != 0])
        min_w0 = 0
        #if wt0[1] > 0:
        #    slope = ZZ(weight_list[1][1]) / ZZ(weight_list[1][0])
        #    assert wt0[1] - slope * wt0[0] >= 0
        #    if wt[1] - slope * wt[0] > 0:
        #        if wt0[1] - slope * wt0[0] == 0:
        #            return []
        #        else:
        #            min_w0 = ceil((wt[1] - slope * wt[0])/(wt0[1] - slope * wt0[0]))

        #adjust max_w0 given the list of syzygous monomials.
        degrees = syzygous.get(index)
        if not degrees is None:
            for d in degrees:
                max_w0 = min(max_w0, d[index] - 1)

        all_ws = []
        for w0 in range(min_w0, max_w0 + 1):
            new_syzygous = {}
            #ignore monomials whose degree in the current covariant is more than w0.
            for n in syzygous:
                if n > index:
                    new_syzygous[n] = [d for d in syzygous[n] if d[index] <= w0]
            ws = BinarySexticsCovariants._GetGeneratorsCov(weight_list[1:], (wt[0]-w0*wt0[0], wt[1]-w0*wt0[1]),
                                                           new_syzygous)
            all_ws += [[w0] + w for w in ws]

        if index == 0:
            #sort list before output
            all_ws = [BinarySexticsCovariants.ring.monomial(*w) for w in all_ws]
            all_ws.sort(reverse = True)
            all_ws = [w.degrees() for w in all_ws]
        return all_ws

    def _ComputeBasisAndRelations(self, use_syzygous = True):
       LW = BinarySexticsCovariants.LW
       #leading monomials come first.
       W = BinarySexticsCovariants._GetGeneratorsCov(LW, self.weight, use_syzygous = use_syzygous)
       dim = self.Dimension()
       covs = [BinarySexticsCovariants.ring.monomial(*wt) for wt in W]
       if (dim == 0):
           return [], [], []
       elif dim == len(W):
           return covs, [], covs
       eval_data = []
       R = PolynomialRing(QQ, ["x", "y"])

       for i in range(dim + 5):
           f = RandomSextic(R, 10)
           basic = EvaluateBasicCovariants(f)
           new_eval = [EvaluateMonomial(wt, basic) for wt in W]
           eval_data.append(new_eval)

       p = 101
       eval_mat = Matrix(GF(p), eval_data).transpose()
       print("Computing rank (size {} * {})...".format(len(W), dim))
       rk = eval_mat.rank()
       print("done")
       while (rk < dim):
           print("One more evaluation point (current rank {})".format(rk))
           p = next_prime(p)
           f = RandomSextic(R, 100)
           basic = EvaluateBasicCovariants(f)
           new_eval = [EvaluateMonomial(wt, basic) for wt in W]
           eval_data.append(new_eval)
           eval_mat = Matrix(GF(p), eval_data).transpose()
           rk = eval_mat.rank()

       eval_mat = Matrix(QQ, eval_data).transpose()
       rels = eval_mat.kernel().echelonized_basis()
       rels = [rel.denominator() * rel for rel in rels]
       rels = [r.list() for r in rels]
       C_basis = [BinarySexticsCovariants.ring.monomial(*W[i]) for i in eval_mat.pivot_rows()]
       assert len(C_basis) == dim
       return C_basis, rels, covs

    def GetBasisAndRelations(self, use_syzygous = False):
        r"""
        Return the generators and relations for the covariants in the space of covariants of binary sextics

        OUTPUT: a list of polynomials in the covariants that generate the space, and a list of polynomial relations that they satisfy

        EXAMPLES:

        This example is Example 2.1 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,0)
            sage: bsc.GetBasisAndRelations()
            ([Co60, Co20*Co40, Co20^3], [])

        This example is the Example commeneted out after Example 2.4 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,8)
            sage: bsc.GetBasisAndRelations()
            ([Co32*Co36, Co28*Co40, Co24*Co44, Co20*Co24^2, Co20^2*Co28, Co16*Co20*Co32],
             [5*Co20*Co24^2 + 4*Co32*Co36 - 10*Co28*Co40 + Co24*Co44 - 60*Co16*Co52])

        This example is Igusa's relation for the Siegel three-fold. ::

            sage: bsc = BinarySexticsCovariants(30,0)
            sage: basis, rels = bsc.GetBasisAndRelations()
            sage: rels
            [1953125*Co20^9*Co40^3 - 15000000*Co20^7*Co40^4 - 1171875*Co20^8*Co40^2*Co60 + 43200000*Co20^5*Co40^5 + 4125000*Co20^6*Co40^3*Co60 + 234375*Co20^7*Co40*Co60^2 - 55296000*Co20^3*Co40^6 + 2160000*Co20^4*Co40^4*Co60 + 900000*Co20^5*Co40^2*Co60^2 - 15625*Co20^6*Co60^3 + 1687500*Co20^6*Co40^2*Co100 + 26542080*Co20*Co40^7 - 20736000*Co20^2*Co40^5*Co60 - 6048000*Co20^3*Co40^3*Co60^2 - 375000*Co20^4*Co40*Co60^3 - 9720000*Co20^4*Co40^3*Co100 - 675000*Co20^5*Co40*Co60*Co100 + 18579456*Co40^6*Co60 + 6635520*Co20*Co40^4*Co60^2 + 806400*Co20^2*Co40^2*Co60^3 + 30000*Co20^3*Co60^4 + 18662400*Co20^2*Co40^4*Co100 + 2592000*Co20^3*Co40^2*Co60*Co100 + 67500*Co20^4*Co60^2*Co100 - 55296*Co40^3*Co60^3 - 11520*Co20*Co40*Co60^4 - 11943936*Co40^5*Co100 - 2488320*Co20*Co40^3*Co60*Co100 + 486000*Co20^3*Co40*Co100^2 + 1152*Co60^5 - 248832*Co40^2*Co60^2*Co100 - 25920*Co20*Co60^3*Co100 - 933120*Co20*Co40^2*Co100^2 - 97200*Co20^2*Co60*Co100^2 + 93312*Co40*Co60*Co100^2 + 46656*Co100^3 + 14929920000000000*Co150^2]

        """
        C_basis, rels, covs = self._ComputeBasisAndRelations(use_syzygous = use_syzygous)
        rels_symb = [sum([rel[i]*covs[i] for i in range(len(covs))]) for rel in rels]
        return C_basis, rels_symb

    def GetBasis(self):
        r"""
        Return the generators for the covariants in the space of covariants of binary sextics

        OUTPUT: a list of polynomials in the covariants that generate the space

        EXAMPLES:

        This example is Example 2.1 in the overleaf. :

            sage: bsc = BinarySexticsCovariants(6,0)
            sage: bsc.GetBasis()
            [Co60, Co20*Co40, Co20^3]

        This example is the Example commeneted out after Example 2.4 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,8)
            sage: bsc.GetBasis()
            [Co32*Co36, Co28*Co40, Co24*Co44, Co20*Co24^2, Co20^2*Co28, Co16*Co20*Co32]

        """
        basis, _ = self.GetBasisAndRelations(use_syzygous = True)
        return basis

    def GetBasisWithConditions(self, p = 0, cusp = False):
        r"""
        Return a set of linearly independent elements in the space of covariants that is
        sufficient to generate the space of holomorphic Siegel modular forms of the
        corresponding weight

        OUTPUT: a list of polynomial in the basic covariants

        EXAMPLES: todo
        """

        B = self.GetBasis()
        if len(B) == 0:
            return []
        W = [b.exponents()[0] for b in B]
        if p == 0:
            R = PolynomialRing(QQ, ["x", "y"])
        else:
            R = PolynomialRing(GF(p), ["x", "y"])
        x = R.gen(0)
        y = R.gen(1)
        eval_data = []
        dim = len(B)
        n = self.a - (self.b)/2
        #if n is odd, we only have cusp forms anyway.
        cusp = cusp or (n % 2 == 1)

        print("GetBasisWithConditions: starting dimension {}, collecting data...".format(dim))
        for k in range(dim + 4):
            f = RandomSextic(R, 4, zeroa5a6 = True)
            mat = RandomSL2(10)
            fp = QuarticTransform(f, mat)
            basic = EvaluateBasicCovariants(f, leading_coefficient = False)
            basicp = EvaluateBasicCovariants(fp, leading_coefficient = False)
            a4 = f.coefficient(x**2 * y**4)
            a4p = fp.coefficient(x**2 * y**4)

            #evaluate basis elements
            new_eval_all = EvaluateMonomials(W, [basic, basicp])
            new_eval = [pol.coefficients(sparse = False) for pol in new_eval_all[0]]
            new_evalp = [pol.coefficients(sparse = False) for pol in new_eval_all[1]]

            #padding in case the evaluation has smaller degree
            for v in new_eval:
                v += [0 for i in range(self.b + 1 - len(v))]
            for v in new_evalp:
                v += [0 for i in range(self.b + 1 - len(v))]
            #these are polynomials in QQ[x] of degree self.b, all coefficients
            #except leading term must vanish
            for i in range(self.b):
                eval_data.append([v[i] for v in new_eval])
                eval_data.append([v[i] for v in new_evalp])
            #additionally, leading coefficient divided by a4^n must be an invariant of quadrics
            #if cusp, must be zero
            if cusp:
                eval_data.append([v[self.b] for v in new_eval])
                eval_data.append([v[self.b] for v in new_evalp])
            else:
                line = [a4p ** (n//2) * new_eval[i][self.b]
                        - a4 ** (n//2) * new_evalp[i][self.b] #no det since SL
                        for i in range(len(B))]
                eval_data.append(line)

        #do linear algebra
        if p == 0:
            print("GetBasisWithConditions: linear algebra over Fp...")
            p = random_prime(10000, lbound = 5000)
            mat = Matrix(GF(p), eval_data)
            rows = mat.pivot_rows()
            print("GetBasisWithConditions: found dimension {}".format(dim - len(rows)))
            mat = Matrix(QQ, [eval_data[i] for i in rows])
            print("GetBasisWithConditions: linear algebra over QQ (size {} x {}, height {})...".format(len(rows), dim, mat.height().global_height()))
            ker = mat.right_kernel().basis_matrix()
            ker = ker * ker.denominator()
            ker = ker.change_ring(ZZ)
            if dim - len(rows) > 1:
                print("GetBasisWithConditions: lattice reduction...")
                ker = ker.LLL()
            print("GetBasisWithConditions: saturation...")
            ker = ker.saturation()
        else:
            print("GetBasisWithConditions: linear algebra over Fp...")
            mat = Matrix(GF(p), eval_data)
            ker = mat.right_kernel().basis_matrix()
            print("GetBasisWithConditions: found dimension {}".format(ker.nrows()))

        res = []
        for LC in ker:
            cov = 0
            for i in range(len(LC)):
                cov += LC[i] * B[i]
            res.append(cov)
        return res

    def ConstructGroebnerBasis():
        BinarySexticsCovariants.SyzygousMonomials = {}
        BinarySexticsCovariants.gbasis = []
        for j in range(0, 25, 2):
            nb = 0
            for k in range(2, 49):
                print("ConstructGroebnerBasis: k = {}, j = {}".format(k, j))
                S = BinarySexticsCovariants(k, j)
                # compute rels as a list of tuples
                _, rels, covs = S._ComputeBasisAndRelations(use_syzygous = True)
                for r in rels:
                    # add polynomial to gbasis, and leading term to SyzygousMonomials
                    pol = BinarySexticsCovariants.ring(0)
                    for i in range(len(r)):
                        pol += r[i] * covs[i]
                    BinarySexticsCovariants.gbasis.append(pol)

                    mon = pol.lm()
                    d = mon.degrees()
                    index = 0
                    for i in range(26):
                        if d[i] > 0:
                            index = i
                    print("k = {}, j = {}, adding monomial {}".format(k, j, mon))
                    if index in BinarySexticsCovariants.SyzygousMonomials.keys():
                        BinarySexticsCovariants.SyzygousMonomials[index].append(mon)
                    else:
                        BinarySexticsCovariants.SyzygousMonomials[index] = [mon]
                    nb += 1
            print("total j = {}: {}".format(j, nb))
        BinarySexticsCovariants.gbasis.sort(reverse = True)

    def PrintGroebnerBasis(filename = "Groebner.dat"):
        with open(filename, "w") as f:
            for x in BinarySexticsCovariants.gbasis:
                f.write(str(x))
                f.write("\n")

    def ReadGroebnerBasis(filename = "Groebner.dat"):
        R = BinarySexticsCovariants.ring
        BinarySexticsCovariants.gbasis = []
        BinarySexticsCovariants.SyzygousMonomials = {}
        with open(filename) as f:
            for line in f:
                BinarySexticsCovariants.gbasis.append(R(line))
        for pol in BinarySexticsCovariants.gbasis:
            mon = pol.lm()
            d = mon.degrees()
            index = 0
            for i in range(26):
                if d[i] > 0:
                    index = i
            if index in BinarySexticsCovariants.SyzygousMonomials.keys():
                BinarySexticsCovariants.SyzygousMonomials[index].append(mon)
            else:
                BinarySexticsCovariants.SyzygousMonomials[index] = [mon]

    #Somehow we can't let Sage know we already have a Gröbner basis, so we have to reimplement this by hand.
    def Reduce(covariant):
        gbasis = BinarySexticsCovariants.gbasis
        cur = covariant
        LM = [x.lm() for x in gbasis]
        LC = [x.lc() for x in gbasis]
        LD = [m.degrees() for m in LM]
        index = 0
        while index < len(cur.monomials()): #reduce monomial until not divisible by anything in gbasis
            m = cur.monomials()[index]
            c = cur.coefficients()[index]
            d1 = m.degrees()
            index += 1
            for i in range(len(LM)):
                div = True
                d2 = LD[i]
                for j in range(len(d1)):
                    if d2[j] > d1[j]:
                        div = False
                        break
                if div:
                    index -= 1 #try again at this index
                    d = [d1[i] - d2[i] for i in range(len(d1))]
                    mdiv = BinarySexticsCovariants.ring.monomial(*d)
                    cur = cur - (c / LC[i]) * mdiv * gbasis[i]
                    break
        return cur

try:
    BinarySexticsCovariants.ReadGroebnerBasis()
except:
    BinarySexticsCovariants.ConstructGroebnerBasis()
