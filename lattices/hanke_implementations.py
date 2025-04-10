import os
from functools import reduce

from sage.arith.misc import kronecker, prime_divisors
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from sage.interfaces.magma import magma
from sage.matrix.constructor import matrix
from sage.structure.element import Matrix
from sage.misc.functional import is_even, is_odd
from sage.misc.misc_c import prod
from sage.quadratic_forms.genera.genus import Genus_Symbol_p_adic_ring
from sage.quadratic_forms.genera.genus import GenusSymbol_global_ring
from sage.rings.integer_ring import ZZ
from sage.rings.integer import Integer
from sage.modules.free_quadratic_module import FreeQuadraticModule_submodule_with_basis_pid, FreeQuadraticModule
from sage.modules.free_quadratic_module_integer_symmetric import IntegralLattice, local_modification
from sage.rings.finite_rings.finite_field_constructor import GF

def algo3_8(L, a=2):
    '''
    INPUT: L : IntegralLattice, a: Integer
    Returns the overlattice of L that is saturated at a
    '''
    # step 2 - skip? should be able to assume B(L, L) in a

    # step 3
    saturated = False
    while not saturated:
        #print(L)
        l = a
        LGenus = L.genus()
        saturated = True
        # compute m_{p, a}
        for symbol in LGenus.local_symbols():
            p = symbol.prime()
            #print(symbol)
            #print(p)
            #print(symbol._symbol[-1][0])
            l *= p ** ((symbol._symbol[-1][0] - ZZ(a).valuation(p) + 1) // 2)
            if (symbol._symbol[-1][0] - ZZ(a).valuation(p) > 1):
                saturated = False
        #print("l:", l)
        #print(l * L.dual_lattice())
        L = L.overlattice((l * L.dual_lattice()).basis())
        #print("Done getting overlattice\n")
    return L

def algo3_11():
    pass

def algo3_12():
    pass

def algo3_13():
    pass


#H5 = Matrix(ZZ, 2, [2,1,1,-2])
#algo3_8(IntegralLattice(H5))