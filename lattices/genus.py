from functools import reduce

from sage.rings.integer_ring import ZZ
from sage.combinat.integer_vector_weighted import WeightedIntegerVectors
from sage.arith.misc import prime_divisors
from sage.misc.misc_c import prod
from sage.quadratic_forms.genera.genus import Genus_Symbol_p_adic_ring
from sage.quadratic_forms.genera.genus import GenusSymbol_global_ring
from sage.interfaces.magma import magma
from sage.matrix.constructor import matrix

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

def encode_rank(rk):
    assert rk >= 0
    if (rk < 10):
        return str(rk)
    if (rk < 10 + 26):
        return chr(ord('a') + (rk - 10))
    assert rk < 10 + 26*2
    return chr(ord('A') + (rk - 10 - 26))

def create_genus_label(genus_sym):
    rk = genus_sym.rank()
    sig = genus_sym.signature()
    det = genus_sym.determinant()
    primes = (2*det).prime_divisors()
    local_symbols = [genus_sym.local_symbol(p).symbol_tuple_list() for p in primes]
    local_symbols_filtered = [genus_sym.local_symbol(p).symbol_tuple_list() for p in primes if det.valuation(p) > 1]
    max_vals = [s[-1][0] for s in local_symbols_filtered]
    rks = [[0 for i in range(max_val)] for max_val in max_vals]
    for i, s in enumerate(local_symbols_filtered):
        for t in s:
            if t[0] > 0:
                rks[i][t[0]-1] = t[1]
    jordan_ranks = ["".join([encode_rank(r) for r in rk]) for rk in rks]

    # we start by encoding the local symbol at 2
    
    s2 = genus_sym.local_symbol(2)
    block_n = s2.number_of_blocks()
    train_ends = [x[-1] for x in s2.trains()]
    assert train_ends[-1] == block_n-1

    # The following can be made more efficient, but I really want to keep track of the single bits in the encoding for now,
    # for debbugging purposes
    bits = []
    # compartments are in correspondece with subsets of {0..block_n-1}
    comparts = reduce(lambda x,y:x+y, s2.compartments(),[])
    compart_symbol = sum([1 << e for e in comparts])
    # note that the compart_symbol will be even if and only if the lattice is even
    compart_nbits = block_n
    bits += ZZ(compart_symbol).digits(2, padto=compart_nbits) 
    
    oddities = [sum([s2.canonical_symbol()[t][4] for t in cmpart]) % 8 for cmpart in s2.compartments()]
    oddities_symbol = sum([o*(1 << (3*i)) for i,o in enumerate(oddities)])
    oddities_nbits = 3*len(s2.compartments())
    bits += ZZ(oddities_symbol).digits(2, padto=oddities_nbits)  
    
    signs = [s2.canonical_symbol()[train[0]][2] for train in s2.trains()]
    bits += [ZZ(1-s) // 2 for s in signs]

    assert primes[0] == 2
    for p in primes[1:]:
        s = genus_sym.local_symbol(p)
        signs = [t[2] for t in s.symbol_tuple_list()]        
        bits += [ZZ(1-s) // 2 for s in signs]
        
    local_data = sum([bits[i] << i for i in range(len(bits))])
    label = ".".join([str(x) for x in [rk,sig,det] + jordan_ranks + [hex(local_data)[2:]]])
    return label

def decode_rank(c):
    assert ((ord('0') <= ord(c) <= ord('9')) or (ord('a') <= ord(c) <= ord('z')) or (ord('A') <= ord(c) <= ord('Z')))
    if (ord('0') <= ord(c) <= ord('9')):
        return ord(c) - ord('0')
    if (ord('a') <= ord(c) <= ord('z')):
        return ord(c) - ord('a') + 10
    assert (ord('A') <= ord(c) <= ord('Z'))
    return ord(c) - ord('A') + 10 + 26

def build_compartments_and_trains(symbols, num_blocks_2, compart_bits):
    compartments = []
    trains = []
    in_compartment = False
    train_start = 0
    for i in range(num_blocks_2):
        if i > 0:
            scale_diff = symbols[0][i][0] - symbols[0][i-1][0]
            if (scale_diff > 2) and (i > train_start):
                trains.append([j for j in range(train_start,i)])
                train_start = i
            
        if compart_bits[i] == 1:
            if in_compartment:
                if (i > 0) and (scale_diff > 1):
                    compartments.append([j for j in range(compart_start, i)])
                    compart_start = i
            if not in_compartment:
                compart_start = i
                in_compartment = True
                if (i > train_start) and (scale_diff > 1):
                    trains.append([j for j in range(train_start,i)])
                    train_start = i
        else: # compart_bits[i] == 0
            if in_compartment:
                in_compartment = False
                compartments.append([j for j in range(compart_start, i+1)])
                if (i > train_start) and (scale_diff == 2):
                    trains.append([j for j in range(train_start,i)])
                    train_start = i
            else:
                if (i > train_start):
                    trains.append([j for j in range(train_start,i)])
                    train_start = i
                
    if in_compartment:
        compartments.append([j for j in range(compart_start, num_blocks_2)])

    trains.append([j for j in range(train_start, num_blocks_2)])
    return compartments, trains


def genus_symbol_from_label(label):
    '''
    Returns a genus symbol corresponding to an LMFDB label.

    :param label: str
    :return: GenusSymbol_global_ring

    >>> all_syms = all_genus_symbols(8,0,2**5*3**4*5**3*7**2,is_even=False)
    >>> all([genus_symbol_from_label(create_genus_label(s)) == s for s in all_syms])
    True
    '''
    split_label = label.split(".")
    rk = ZZ(split_label[0])
    sig = ZZ(split_label[1])
    n_plus = (rk + sig) // 2
    n_minus = (rk - sig) // 2
    det = ZZ(split_label[2])
    primes = (2*det).prime_divisors()
    symbols = []
    for i,p in enumerate(primes):
        rank_dec = [decode_rank(c) for c in split_label[3+i]]
        rank_dec = [rk - sum(rank_dec)] + rank_dec
        symbols_p = [[i, rank_dec[i], 1] for i in range(len(rank_dec)) if rank_dec[i] > 0]
        symbols.append(symbols_p)

    # initializing the symbol at 2
    symbols[0] = [s + [0,0] for s in symbols[0]]
    num_blocks_2 = len(symbols[0])
    
    local_data = ZZ(split_label[3 + len(primes)], base=16)

    compart_bits = (local_data % (1 << num_blocks_2)).digits(2, padto=num_blocks_2)

    for i in range(num_blocks_2):
        symbols[0][i][3] = compart_bits[i]

    compartments, trains = build_compartments_and_trains(symbols, num_blocks_2, compart_bits)
            
    local_data >>= num_blocks_2
    
    oddity_bits = (local_data % (1 << (3*len(compartments)))).digits(2, padto=3*len(compartments))

    oddity_nums = [oddity_bits[3*i:3*(i+1)] for i in range(len(compartments))]
    oddities = [sum([(b[i] << i) for i in range(3)]) for b in oddity_nums]

    # updating oddities
    
    for j,c in enumerate(compartments):
        symbols[0][c[0]][4] = oddities[j]

    local_data >>= 3 * len(compartments)

    # train_signs = [i for i in range(len(trains)) if (local_data.bits()[i+offset] == 1)]

    train_sign_bits = (local_data % (1 << len(trains))).digits(2, padto=len(trains))

    # updating signs at 2
    
    for t,train in enumerate(trains):
        sign = (-1)**(train_sign_bits[t])
        symbols[0][train[0]][2] = 3 if sign == -1 else 1

    local_data >>= len(trains)

    for j in range(1, len(symbols)):
        n = len(symbols[j])
        sign_bits = (local_data % (1 << n)).digits(2, padto=n)
        for i in range(n):
            symbols[j][i][2] = (-1)**(sign_bits[i])
        local_data >>= n

    local_symbols = [Genus_Symbol_p_adic_ring(p, symbols[j]) for j,p in enumerate(primes)]
    return GenusSymbol_global_ring((n_plus, n_minus), local_symbols)

# This is based on the __repr__ method from local symbols
# !! TODO !! - should refactor the code there and then use it

def conway_symbol_diadic(local_symbol):
    CS = local_symbol.canonical_symbol()
    trains = local_symbol.trains()
    comps = local_symbol.compartments()

    # removing the 0-index in case we omit it
        
    if CS[0][0] == 0:
        if trains[0] == [0]:
            trains = trains[1:]
        else:
            trains = [trains[0][1:]] + trains[1:]
            
        if len(comps) > 0:
            if comps[0] == [0]:
                comps = comps[1:]
            elif comps[0][0] == 0:
                comps = [comps[0][1:]] + comps[1:]
                
            
    for train in trains:
        # mark the beginning of a train with a colon
        CS_string += " :"
        # collect the indices where compartments begin and end
        compartment_begins = []
        compartment_ends = []
        for comp in comps:
            compartment_begins.append(comp[0])
            compartment_ends.append(comp[-1])

        for block_index in train:
            if block_index in compartment_begins:
                # mark the beginning of this compartment with [
                CS_string += "["
            block = CS[block_index]
            block_string = "%s^{%s}" % (p**block[0], block[2] * block[1])
            CS_string += block_string
            if block_index in compartment_ends:
                # close this compartment with ]
                CS_string += "]"
                # the oddity belongs to the compartment
                # and is saved in its first block
                i = compartment_ends.index(block_index)
                compartment_start = compartment_begins[i]
                oddity = CS[compartment_start][4]
                CS_string += "_%s" % oddity
        # remove the first colon
        CS_string = CS_string[2:]
        # remove some unnecessary whitespace
        CS_string = CS_string.replace("  :", ":")
    return CS_string

# Here we do not want the trains and compartments, for the global symbol
def conway_symbol_local_part(local_symbol):
    p = local_symbol.prime()
    CS_string = ""
    symbols = local_symbol.canonical_symbol()
    if (p == 2) and (symbols[0][3] == 0):
        oddities = [i for i,s in enumerate(symbols) if s[4] != 0]
        if len(oddities) > 0:
            last_idx = oddities[-1]
            # we won't display the oddity when it can be inferred from the oddity formula
            symbols[last_idx][4] = 0
            
    symbols = [s for s in symbols if s[0] > 0]
    for s in symbols:
        CS_string += "%s^{%s}" % (p**s[0], s[2] * s[1])
        if (p == 2) and ((s[1] % 2 == 0) or (s[1] == 1)):
            if s[3] == 0:
                CS_string += "_{II}"
            else:
                if s[4] == 0:
                    CS_string += "_{I}"
                else:
                    CS_string += "_{" + str(s[4]) + "}"
    return CS_string

def conway_symbol(genus_symbol):
    roman_numeral = "II" if genus_symbol.is_even() else  "I"
    r,s = genus_symbol.signature_pair()
    prefix = roman_numeral + "_{" + str(r) + "," + str(s) + "}"
    local_part = "".join([conway_symbol_local_part(s) for s in genus_symbol.local_symbols()])
    return prefix + "(" + local_part + ")"

def flat_mat(mat):
    rows = [list(x) for x in mat.rows()]
    return reduce(lambda x,y: x+y, rows)

def create_genus_entry(genus_symbol, hecke_primes=[2]):
    '''
    Returns a dictionary with fields corresponding to the schema, 
    and values populated by the genus symbol.
    The list of hecke_primes determines for which primes we compute
    the Hecke matrices and Hecke polynomials
    '''
    table_row = {}
    table_row['label'] = create_genus_label(genus_symbol)
    table_row['rank'] = genus_symbol.rank()
    table_row['signature'] = genus_symbol.signature_pair()[0]
    table_row['det'] = genus_symbol.determinant()
    table_row['disc'] = table_row['det']
    if (genus_symbol.is_even() and genus_symbol.rank() % 2 == 1):
        table_row['disc'] *= 2
    table_row['conway_symbol'] = conway_symbol(genus_symbol)
    table_row['level'] = genus_symbol.level()
    table_row['is_even'] = genus_symbol.is_even()
    disc_form = genus_symbol.discriminant_form()
    table_row['discriminant_group_invs'] = disc_form.invariants()
    disc_q = disc_form.gram_matrix_quadratic()
    den = disc_q.denominator()
    table_row['discriminant_form'] = flat_mat(den*disc_q)
    
    # These operations are time consuming, and in high rank should be replaced by Noam's code
    h = len(genus_symbol.representatives())
    table_row['class_number'] = h

    mass = genus_symbol.mass()
    table_row['mass'] = [mass.numerator(), mass.denominator()]
    
    lat = genus_symbol.representative()
    hecke_mats = {}
    hecke_polys = {}
    for p in hecke_primes:
        hecke_mag = magma.AdjacencyMatrix(magma.Genus(magma.LatticeWithGram(lat)),p)
        hecke_mats[p] = list(magma.Eltseq(hecke_mag))
        hecke_mat = matrix(ZZ, h, h, hecke_mats[p])
        hecke_poly_fac = list(hecke_mat.charpoly().factor())
        hecke_polys[p] = [[fa[0].list(), fa[1]] for fa in hecke_poly_fac]
    table_row['adjacency_matrix'] = hecke_mats
    table_row['adjacency_polynomials'] = hecke_polys
    
    return table_row
    
