import lasVegas
from importlib import reload
reload(lasVegas)
import genus
reload(genus)
import time

import os
from functools import reduce
from line_profiler import LineProfiler

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
from random import randint, choice
from math import prod
from itertools import product

def dhTest(testCases):
    print("Dubey Holenstein algorithm start.")
    cache = {}
    start = time.time()
    for i, test in enumerate(testCases):
        print(lasVegas.symbolList(test))
        lasVegas.dubeyHolensteinLatticeRepresentative(test, check=False,superDumbCheck=False,cache=cache)
        if i%5 == 4:
            print(f"{i+1} of {len(testCases)} done.")
    end = time.time()
    print(f"Dubey Holenstein algorithm complete in {round(end-start, 2)} seconds.")
    print(f"Cache size: {len(cache)}")

def sageTest(testCases):
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

def getRandomSymbol(det, rank):
    if det < 0:
        n_minus = 1
        n_plus = rank-1
    else:
        n_minus = 0
        n_plus = rank
    primes = ZZ(2*det).prime_divisors()
    odd_primes = primes[1:]
    global_symbs = []
    symbList = []
    for p in odd_primes:
        possibilities = genus.all_local_genus_symbols(rank, det, p)
        assert len(possibilities) > 0, f"no symbols at p={p}"
        symbList.append(choice(possibilities))
    
    dyadic = genus.all_dyadic_genus_symbols(n_plus, n_minus, det, symbList, only_even=True)
    assert len(dyadic) > 0, f"no symbols at p=2"
    symbList.insert(0,choice(dyadic))
    return GenusSymbol_global_ring((n_plus, n_minus), symbList)

def dhTimeProfile(method, globalGenus):
    lp = LineProfiler()
    lp.add_function(method)
    lp_wrapper = lp(lasVegas.dubeyHolensteinLatticeRepresentative)
    lp_wrapper(globalGenus)
    lp.print_stats()

def printbar():
    print("___________________\n")



if __name__ == "__main__":
    signaturePair = (ZZ(45),ZZ(0))
    det = 24
    actualTests = cut(genus.all_genus_symbols(signaturePair[0], signaturePair[1], det),1)
    # actualTests = [lasVegas.genusFromSymbolLists((11,0),[
    #     (2,     [[2, 4, 1, 1, 4], [3, 4, 5, 0, 0], [4, 3, 3, 1, 1]]),
    #     (100000007,     [[0, 10, 1], [3, 1, 1]])
    # ])]

    print(f"Running {len(actualTests)} tests.")
    printbar()

    #run tests
    dhTest(actualTests)
    printbar()
    sageTest(actualTests)

    # dhTimeProfile(lasVegas.computeChangeOfVariables, actualTests[0])
    