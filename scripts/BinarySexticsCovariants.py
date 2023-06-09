"""
This file contains functions to compute a basis for the space of covariants of binary sextics C_{a,b} of degree a and order b.
"""

## imports
from functools import reduce
from sage.structure.sage_object import SageObject
from sage.all import Matrix, Partitions, ZZ, QQ, prod, Set
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from Generators_Ring_Covariants_Sextic import GetRingGeneratorsCov

# we use a class in order to perform initialization only once

class BinarySexticsCovariants(SageObject):

    r"""
     Constructs spaces of covariants of binary sextics

     EXAMPLES:
    
     This example is Example 2.1 in the overleaf. ::

        sage: bsc = BinarySexticsCovariants(6,0)
        sage: bsc.GetBasisAndRelationsCov()
        ([Co60, Co20*Co40, Co20^3], [])
        
    """
    
    LW, LCo, LCov = GetRingGeneratorsCov()

    # Verifying the expression for C_{2,0}
    assert LCo[1].parent().variable_names()[1] == 'Co20'
    a = LCov[1].base_ring().gens()
    assert LCov[1] == -3*a[3]**2 + 8*a[2]*a[4] - 20*a[1]*a[5] + 120*a[0]*a[6]
    
    def __init__(self, a, b):
        self.a = a
        self.b = b
        self.weight = (a,b)

    def MakeCov(L):
        r"""
        Returns a list with two elements, the first is the polynomial in the covariants defined by the exponents in L, and the second is
        its evaluation at the covariants (polynomial in the a_i, x and y)

        INPUT:

        - ``L`` - a list of exponents for the different covariants.
        
        OUTPUT: [Cov, polynomial in a_i and x,y]

        EXAMPLES:

        This example is Example 2.3 in the overleaf. ::

           sage: bsc = BSC(6,0)
           sage: W = BSC.GetGeneratorsCov(BSC.LW, bsc.weight)
           sage: covs = [BSC.MakeCov(wt) for wt in W]
           sage: covs[1]
           [Co20*Co40,
            -9*a3^6 + 72*a2*a3^4*a4...
        
        """
        S = [[BinarySexticsCovariants.LCo[k]**L[k],BinarySexticsCovariants.LCov[k]**L[k]] for k in range(len(L))]
        S1 = prod(S[k][0] for k in range(len(S)))
        S2 = prod(S[k][1] for k in range(len(S)))
        return [S1,S2]

    # Somehow this is slow if one runs it line by line, but quite fast in practice ?!
    def GetGeneratorsCovSlow(weight_list, wt):
        has_zero = [ any([x[i] == 0 for x in weight_list]) for i in range(2)]
        assert not all(has_zero)
        if (has_zero[1]) or ((not has_zero[0]) and (wt[0] < wt[1])):
            return BinarySexticsCovariants.GetGeneratorsCov([[x[1],x[0]] for x in weight_list], [wt[1], wt[0]])
        exps = list(WeightedIntegerVectors(wt[1],[x[1] for x in weight_list]))
        return [exp for exp in exps if sum([exp[i]*weight_list[i][0] for i in range(len(exp))]) == wt[0]]

    def GetGeneratorsCov(weight_list, wt):
        if (len(weight_list) == 0):
            if (wt == (0,0)):
                return [[]]
            else:
                return []
        wt0 = weight_list[0]
        assert not ((wt0[0] == 0) and (wt0[1] == 0))
        max_w0 = min([wt[i] // wt0[i] for i in range(2) if wt0[i] != 0])
        all_ws = []
        for w0 in range(max_w0+1):
            ws = BinarySexticsCovariants.GetGeneratorsCov(weight_list[1:], (wt[0]-w0*wt0[0], wt[1]-w0*wt0[1]))
            all_ws += [[w0] + w for w in ws]
        return all_ws

    def Dimension(self):
        # using he Cayley-Sylvester formula
        a = self.a
        b = self.b
        n = 3 * a - b // 2
        def p(k,n):
            return Partitions(n,max_length=k, max_part=6).cardinality()
        return p(a,n) - p(a,n-1)
    
    def GetBasisAndRelationsCov(self):
        r"""
        Return the generators and relations for the covariants in the space of covariants of binary sextics

        OUTPUT: a list of polynomials in the covariants that generate the space, and a list of polynomial relations that they satisfy

        EXAMPLES:

        This example is Example 2.1 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,0)
            sage: bsc.GetBasisAndRelationsCov()
            ([Co60, Co20*Co40, Co20^3], [])

        This example is the Example commeneted out after Example 2.4 in the overleaf. ::

            sage: bsc = BinarySexticsCovariants(6,8)
            sage: bsc.GetBasisAndRelationsCov()
            ([Co32*Co36, Co28*Co40, Co24*Co44, Co20*Co24^2, Co20^2*Co28, Co16*Co20*Co32],
             [5*Co20*Co24^2 + 4*Co32*Co36 - 10*Co28*Co40 + Co24*Co44 - 60*Co16*Co52])

        This example is Igusa's relation for the Siegel three-fold. ::

            sage: bsc = BinarySexticsCovariants(30,0)
            sage: basis, rels = bsc.GetBasisAndRelationsCov()
            sage: rels
            [1953125*Co20^9*Co40^3 - 15000000*Co20^7*Co40^4 - 1171875*Co20^8*Co40^2*Co60 + 43200000*Co20^5*Co40^5 + 4125000*Co20^6*Co40^3*Co60 + 234375*Co20^7*Co40*Co60^2 - 55296000*Co20^3*Co40^6 + 2160000*Co20^4*Co40^4*Co60 + 900000*Co20^5*Co40^2*Co60^2 - 15625*Co20^6*Co60^3 + 1687500*Co20^6*Co40^2*Co100 + 26542080*Co20*Co40^7 - 20736000*Co20^2*Co40^5*Co60 - 6048000*Co20^3*Co40^3*Co60^2 - 375000*Co20^4*Co40*Co60^3 - 9720000*Co20^4*Co40^3*Co100 - 675000*Co20^5*Co40*Co60*Co100 + 18579456*Co40^6*Co60 + 6635520*Co20*Co40^4*Co60^2 + 806400*Co20^2*Co40^2*Co60^3 + 30000*Co20^3*Co60^4 + 18662400*Co20^2*Co40^4*Co100 + 2592000*Co20^3*Co40^2*Co60*Co100 + 67500*Co20^4*Co60^2*Co100 - 55296*Co40^3*Co60^3 - 11520*Co20*Co40*Co60^4 - 11943936*Co40^5*Co100 - 2488320*Co20*Co40^3*Co60*Co100 + 486000*Co20^3*Co40*Co100^2 + 1152*Co60^5 - 248832*Co40^2*Co60^2*Co100 - 25920*Co20*Co60^3*Co100 - 933120*Co20*Co40^2*Co100^2 - 97200*Co20^2*Co60*Co100^2 + 93312*Co40*Co60*Co100^2 + 46656*Co100^3 + 14929920000000000*Co150^2]
        
        """
        W = BinarySexticsCovariants.GetGeneratorsCov(BinarySexticsCovariants.LW, self.weight)
        covs = [BinarySexticsCovariants.MakeCov(wt) for wt in W]
        poly_ring_bivariate = BinarySexticsCovariants.LCov[0].parent()
        coeff_ring = poly_ring_bivariate.base_ring()
        # Here we are using the theorem by Roberts, stating it is enough to consider the coefficient of x^b
        lcs = [coeff_ring(c[1].coefficient([0,self.b])) for c in covs]
        exps = reduce(lambda x,y: x.union(y), [Set(lc.exponents()) for lc in lcs], Set([]))
        # We try to make this more efficient as exps is very long
        maybe_enough_coeffs = 2*len(lcs)
        coeffs_mat = Matrix([[ZZ(lc.coefficient(e)) for e in exps[:maybe_enough_coeffs]] for lc in lcs])
        maybe_rels = coeffs_mat.kernel().basis()
        check_rels = [sum([rel[i]*covs[i][1] for i in range(len(covs))]) for rel in maybe_rels]
        rels = [maybe_rels[i] for i in range(len(maybe_rels)) if check_rels[i] == 0]
        rels_symb = [sum([rel[i]*covs[i][0] for i in range(len(covs))]) for rel in rels]
        ## Fixing C_basis
        add_exps = reduce(lambda x,y: x.union(y), [Set(coeff_ring(check_rels[i].coefficient([0,self.b])).exponents()) for
                                                   i in range(len(maybe_rels)) if check_rels[i] != 0], Set([]))
        all_exps = exps[:maybe_enough_coeffs] + add_exps[:len(add_exps)]
        coeffs_mat = Matrix([[ZZ(lc.coefficient(e)) for e in all_exps] for lc in lcs])
        C_basis = [covs[i][0] for i in coeffs_mat.pivot_rows()]
        assert len(C_basis) == self.Dimension()
        return C_basis, rels_symb
