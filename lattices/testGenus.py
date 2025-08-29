import lasVegas
from importlib import reload
reload(lasVegas)
import genus
reload(genus)
import time

import os
from functools import reduce

from sage.arith.misc import kronecker, prime_divisors, inverse_mod, factor
from sage.arith.functions import LCM_list
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from sage.functions.other import ceil
from sage.interfaces.magma import magma
from sage.matrix.constructor import matrix
from sage.matrix.special import block_diagonal_matrix, diagonal_matrix, block_matrix
from sage.structure.element import Matrix
from sage.misc.functional import is_even, is_odd, sqrt
from sage.misc.misc_c import prod
from sage.quadratic_forms.genera.genus import Genus_Symbol_p_adic_ring
from sage.quadratic_forms.genera.genus import GenusSymbol_global_ring
from sage.quadratic_forms.genera.genus import is_GlobalGenus, is_2_adic_genus
from sage.quadratic_forms.genera.genus import LocalGenusSymbol
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.integer_ring import ZZ
from sage.rings.integer import Integer
from sage.modules.free_quadratic_module import FreeQuadraticModule_submodule_with_basis_pid, FreeQuadraticModule
from sage.modules.free_quadratic_module_integer_symmetric import IntegralLattice, local_modification
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.structure.factorization_integer import IntegerFactorization
from sage.quadratic_forms.genera.normal_form import p_adic_normal_form
from sage.matrix.constructor import zero_matrix
from random import randint
from math import prod
from itertools import product

def compare(testCases):
    print("Dubey Holenstein algorithm start.")
    cache = {}
    start = time.time()
    for i, test in enumerate(testCases):
        lasVegas.dubeyHolensteinLatticeRepresentative(test, check=False,superDumbCheck=False,cache=cache)
        if i%5 == 4:
            print(f"{i+1} of {len(testCases)} done.")
    end = time.time()
    print(f"Dubey Holenstein algorithm complete in {round(end-start, 2)} seconds.")
    print(f"Cache size: {len(cache)}")
    
    print("Sage algorithm start.")
    start = time.time()
    for i, test in enumerate(testCases):
        test.representative()
        if i%5 == 4:
            print(f"{i+1} of {len(testCases)} done.")
    end = time.time()
    print(f"Sage algorithm complete in {round(end-start, 2)} seconds.")

def cut(testCases, targetSize):
    """pick a determined subset of testCases
    
    this is just to get a uniform distribution from the list because of the nature of the ordering of the list (helps catch bugs hopefully)"""
    if targetSize > len(testCases):
        return testCases
    else:
        gap = len(testCases)//targetSize
        return [testCases[i*gap] for i in range(targetSize)]

if __name__ == "__main__":
    signaturePair = (ZZ(6),ZZ(6))
    det = 2**7 * 17**2 * 23**3
    testCases = genus.all_genus_symbols(signaturePair[0], signaturePair[1], det)
    print(f"Loaded {len(testCases)} symbols with determinant {factor(det)} and signature {signaturePair}.")
    actualTests = cut(testCases, 100)
    compare(actualTests)
    
    # test = lasVegas.genusFromSymbolLists((12,6), [(2,[[0, 10, 3, 0, 0], [1, 8, 3, 1, 2]]),
    #                                               (17,[[0, 12, -1], [1, 6, -1]]),
    #                                               (23,[[0, 14, -1], [1, 4, -1]])])

    # # assert is_GlobalGenus(test), f"Test case of:\n{test}is not even a valid genus!"
    # print(f"Symbols:\n{"\n".join([str(i.symbol_tuple_list()) for i in test.local_symbols()])}")
    # print(f"Signature: {test.signature_pair()}")
    # print("Sage algorithm start")
    # assert(Genus(test.representative()) == test)
    # print("Sage algorithm end")
    # print("Dubey Holenstein start")
    # print(f"Representative:\n{lasVegas.dubeyHolensteinLatticeRepresentative(test,check = False,superDumbCheck = False)}\n______")
    