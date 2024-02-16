from functools import reduce

from sage.rings.integer_ring import ZZ
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from sage.arith.misc import prime_divisors
from sage.misc.misc_c import prod
from sage.quadratic_forms.genera.genus import Genus_Symbol_p_adic_ring
from sage.quadratic_forms.genera.genus import GenusSymbol_global_ring

def get_product(set_list):
    '''
    Returns all elements in the cartesian product of the sets in set_list

    :param set_list: list
    :return: list

    >>> get_product([[[1,2],[3,4,5]], [[6,7,8,9],[10]], [[11,12],[13,14,15]]])
    [[[1, 2], [6, 7, 8, 9], [11, 12]],
    [[1, 2], [6, 7, 8, 9], [13, 14, 15]],
    [[1, 2], [10], [11, 12]],
    [[1, 2], [10], [13, 14, 15]],
    [[3, 4, 5], [6, 7, 8, 9], [11, 12]],
    [[3, 4, 5], [6, 7, 8, 9], [13, 14, 15]],
    [[3, 4, 5], [10], [11, 12]],
    [[3, 4, 5], [10], [13, 14, 15]]]

    >>> get_product([])
    [[]]

    >>> get_product([[1]])
    [[1]]
    '''
    if len(set_list) == 0:
        return [[]]
    if len(set_list) == 1:
        return [[x] for x in set_list[0]]
    return [[x] + y for x in set_list[0] for y in get_product(set_list[1:])]

def get_dets(det_set, sign, num):
    '''
    Returns all possible sequences of length num of signs whose product is sign.
    These correspond to the quadratic character of the determinants of Jordan factors.

    :param det_set: list
    :param sign: int
    :param num: int

    :return: list

    >>> get_dets([1,-1],1,3)
    [[1, 1, 1], [-1, 1, -1], [1, -1, -1], [-1, -1, 1]]
    '''
    dets = []
    b = len(det_set)
    num_opts = b**(num - 1)
    for n in range(num_opts):
        idxs = ZZ(n).digits(b, padto=num - 1)
        det = [det_set[idx] for idx in idxs]
        # sgn = sign*prod(det)**(-1)
        # Here we assume signs are 1 or -1
        sgn = sign*prod(det)
        det += [sgn]
        dets.append(det)
    return dets  

def oddity(s):
    '''
    Compute the oddity for a list of quintuples that describe a 2-adic genus symbol
    '''
    odd = sum([t[-1] for t in s])
    k = len([t for t in s if t[0] % 2 == 1 and t[2] in [3,5]])
    odd += 4*k
    odd %= 8
    return odd

def expected_oddity(n_plus, n_minus, odd_symbols):
    '''
    Returns the oddity of the 2-adic genus symbol, given the signature and the p-adic genus symbols at the odd primes.
    This follows from the oddity condition.
    '''
    excess = sum([symb.excess() for symb in odd_symbols])
    return (excess + n_plus - n_minus) % 8

def all_local_genus_symbols(rank, det, p):
    '''
    Returns all possible p-adic genus symbols for a lattice of a given rank and determinant
    '''
    val_det, unit_det = ZZ(det).val_unit(p)
    symbs = []
    det_set = [1,-1]
    sign = unit_det.kronecker(p)
    val_det, unit_det = ZZ(det).val_unit(p)
    decs = WeightedIntegerVectors(val_det, range(1,val_det+1))
    ranks = [[rank-sum(dec)] + list(dec) for dec in decs if sum(dec) <= rank]
    for dec in ranks:
        scls = [i for i in range(len(dec)) if dec[i] > 0]
        rks = [dec[i] for i in scls]
        dets = get_dets(det_set, sign, len(scls))
        for det_list in dets:
            assert prod(det_list) == sign
            blocks = [[scls[j], rks[j], det_list[j]] for j in range(len(rks))]
            blocks.sort()
            symbs.append(blocks)
    return [Genus_Symbol_p_adic_ring(p,symb) for symb in symbs]

def listify_symbol(x):
    return reduce(lambda x,y : x+y, x.canonical_symbol())

def get_unique(symbs):
    '''
    Returns a list containing only one symbol from every equivalence class
    '''
    symb_dict = {}
    for i,s in enumerate(symbs):
        symb_dict[tuple(listify_symbol(s))] = i
    return [symbs[i] for i in symb_dict.values()]

def all_diadic_genus_symbols(n_plus, n_minus, det, odd_symbols, is_even=True):
    '''
    Returns all the possible 2-adic genus symbols of a global genus symbol having a signature (n_plus, m_minus),
    determinant det and p-adic genus symbols odd_symbols at the odd primes p dividing the determinant
    '''
    rank = n_plus + n_minus
    p = 2
    val_det, unit_det = ZZ(det).val_unit(p)
    symbs = []
    det_set = [1,3]
    sign = unit_det.kronecker(p)
    decs = WeightedIntegerVectors(val_det, range(1,val_det+1))
    ranks = [[rank-sum(dec)] + list(dec) for dec in decs if sum(dec) <= rank]
    exp_oddity = expected_oddity(n_plus, n_minus, odd_symbols)
    for dec in ranks:
        scls = [i for i in range(len(dec)) if dec[i] > 0]
        rks = [dec[i] for i in scls]
        dets = get_dets([1,-1], sign, len(scls))
        for det_list in dets:
            assert prod(det_list) == sign
            blocks = [[scls[j], rks[j], det_set[ZZ(1 - det_list[j]) // 2]] for j in range(len(rks))]
            # We do not obtain all oddities.
            comps = []
            for block in blocks:
                oddities = []
                if block[0] == 0:
                    # if the scaling is trivial and we want an even lattice, we cannot have any oddity
                    if is_even:
                        oddities = [[0,0]]
                    else:
                        oddities = [[0,0]] + [[1,o] for o in range(8)]
                elif block[1] == 1:
                    if block[2] == 1: 
                        oddities = [[1,1],[1,7]]
                    else:
                        oddities = [[1,3],[1,5]]
                elif block[1] == 2:
                    if block[2] == 1:
                        oddities = [[0,0],[1,0],[1,2],[1,6]]
                    else:
                        oddities = [[0,0],[1,2],[1,4],[1,6]]
                elif block[1] % 2 == 0:
                    oddities = [[0,0],[1,0],[1,2],[1,4],[1,6]]
                else:
                    oddities = [[1,1],[1,3],[1,5],[1,7]]
                comps.append([block + odd for odd in oddities])
            # !! TODO - replace by something that generated only those with the correct oddity
            for cmps in get_product(comps):
                if (oddity(cmps) - exp_oddity) % 8 == 0:
                    symbs.append(cmps)
    gen_symbs = [Genus_Symbol_p_adic_ring(p,symb) for symb in symbs]
    if is_even:
        assert all([s.is_even() for s in gen_symbs])
    return get_unique(gen_symbs)

def all_genus_symbols(n_plus, n_minus, det, is_even=True):
    '''
    Returns all the genus symbols of even lattices with signature (n_plus, n_minus) and determinant det

    :param n_plus: int
    :param n_minus: int
    :param det: int
    :param is_even: bool
    :return: list

    >>> all_genus_symbols(16,0,1)
    [Genus of
    None
    Signature:  (16, 0)
    Genus symbol at 2:    1^16]

    >>> all_genus_symbols(16,0,1,is_even=False)
    [Genus of
    None
    Signature:  (16, 0)
    Genus symbol at 2:    1^16,
    Genus of
    None
    Signature:  (16, 0)
    Genus symbol at 2:    [1^16]_0]
    
    >>> len(all_genus_symbols(5,0,2*512))
    63

    >>> [len(all_genus_symbols(17,0,2*D)) for D in range(1,10)]
    [1, 1, 1, 3, 1, 2, 1, 3, 3]
    '''
    rank = n_plus + n_minus
    primes = ZZ(2*det).prime_divisors()
    odd_primes = primes[1:]
    global_symbs = []
    odd_symbs = get_product([all_local_genus_symbols(rank, det, p) for p in odd_primes])
    for odd_symbols in odd_symbs:
        diadic = all_diadic_genus_symbols(n_plus, n_minus, det, odd_symbols, is_even=is_even)
        for symb2 in diadic:
            g = GenusSymbol_global_ring((n_plus, n_minus), [symb2] + odd_symbols)
            global_symbs.append(g)
    return global_symbs
    
