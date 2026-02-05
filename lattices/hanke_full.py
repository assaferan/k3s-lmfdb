from sage.all import *
import random
from collections import defaultdict
import itertools


def gcd_extended(a, b):
    if a == 0:
        return b, 0, 1
    gcd, x1, y1 = gcd_extended(b % a, a)
    x = y1 - (b // a) * x1
    y = x1
    return gcd, x, y

def find_min_x(num, rem):
    prod = 1
    for n in num:
        prod *= n

    result = 0
    for i in range(len(num)):
        prod_i = prod // num[i]
        _, inv_i, _ = gcd_extended(prod_i, num[i])
        result += rem[i] * prod_i * inv_i

    return result % prod

def algo3_8(L, a=2):
    saturated = False
    while not saturated:
        # l = a
        l = 1
        LGenus = L.genus()
        saturated = True
        for symbol in LGenus.local_symbols():
            p = symbol.prime()
            # l *= p ** ((symbol._symbol[-1][0] - ZZ(a).valuation(p) + 1) // 2)
            l *= p ** ((symbol._symbol[-1][0] + 1) // 2)
            # if (symbol._symbol[-1][0] - ZZ(a).valuation(p) > 1):
            if (symbol._symbol[-1][0] > 1):
                saturated = False
        L = L.overlattice((l * L.dual_lattice()).basis())
    return L

def B(v, M, w=None):
    rng = M.base_ring()
    try:
        v = vector(rng, [rng(a) for a in v])
    except:
        pass
    if w != None:
        try:
            w = vector(rng, [rng(a) for a in w])
        except:
            pass
    if w is None:
        return (v * M * v.column())[0]
    else:
        return (v * M * w.column())[0]

def _to_field_vector(v, F):
    return vector(F, [F(x) for x in list(v)])

def B_field(v, M, w=None):
    F = M.base_ring()
    vF = _to_field_vector(v, F)
    if w is None:
        return (vF * M * vF.column())[0]
    wF = _to_field_vector(w, F)
    return (vF * M * wF.column())[0]


def radical_and_complement_rows_fp(M):
    """
    Returns (R_rows, Comp_rows) where rows are ambient row-vectors (as Matrix over M.base_ring()).
    """
    F = M.base_ring()
    n = M.nrows()

    # right kernel gives column vectors x with M*x = 0
    K = M.right_kernel()
    K_basis_cols = K.basis()   # list of column vectors (sage column vectors)
    # Radical rows: convert each column vector to a list of scalars
    R_rows = Matrix(F, [ list(col) for col in K_basis_cols ])  # may be 0 x n

    # Build a complement by taking standard basis columns and selecting those that extend span of radical
    base_cols = [ list(col) for col in K_basis_cols ]   # each entry is a length-n list
    comp_cols = []  # will store lists of scalars (each length n)

    for i in range(n):
        e = vector(F, [F(1) if j==i else F(0) for j in range(n)])
        e_list = list(e)
        # test matrix whose columns are base_cols + [e_list] + comp_cols
        test_cols_lists = base_cols + [e_list] + comp_cols
        base_cols_lists = base_cols + comp_cols
        if test_cols_lists:
            mat_test = Matrix(F, test_cols_lists).transpose()   # n x k
        else:
            mat_test = Matrix(F, 0, 0, [])
        if base_cols_lists:
            mat_base = Matrix(F, base_cols_lists).transpose()
        else:
            mat_base = Matrix(F, 0, 0, [])

        if mat_test.rank() > mat_base.rank():
            comp_cols.append(e_list)
        if len(comp_cols) + len(base_cols) >= n:
            break

    if comp_cols:
        Comp_rows = Matrix(F, comp_cols)   # rows = chosen complement vectors
    else:
        Comp_rows = Matrix(F, 0, n, [])

    return R_rows, Comp_rows

def restrict_gram(M, basis_rows):
    F = M.base_ring()
    if basis_rows.nrows() == 0:
        return Matrix(F, 0, 0, [])
    return basis_rows * M * basis_rows.transpose()

def find_isotrop_fp(M, max_trials=200):
    F = M.base_ring()
    n = M.nrows()
    V = VectorSpace(F, n)
    for i in range(n):
        e = V.basis()[i]
        if B_field(e, M) == F(0):
            return e
    for _ in range(max_trials):
        a = V.random_element()
        if a == V.zero():
            continue
        if B_field(a, M) == F(0):
            return a
    return None

def hyperbolic_fp(M):
    F = M.base_ring()
    n = M.nrows()
    V = VectorSpace(F, n)

    v = find_isotrop_fp(M)
    if v is None:
        return None

    for _ in range(3 * n + 10):
        w = V.random_element()
        if w == V.zero():
            continue
        val = B_field(v, M, w)
        if val != F(0):
            inv = val**(-1)
            w = inv * w
            if matrix(F, [list(v), list(w)]).rank() == 2:
                return [v, w]
    for e in V.basis():
        val = B_field(v, M, e)
        if val != F(0):
            w = (val**(-1)) * e
            if matrix(F, [list(v), list(w)]).rank() == 2:
                return [v, w]
    return None

def max_isotrop_fp(M, verbose=False):
    F = M.base_ring()
    n = M.nrows()

    R_rows, B_rows = radical_and_complement_rows_fp(M)
    radical_ambient = [ vector(F, list(r)) for r in R_rows.rows() ]

    if B_rows.nrows() == 0:
        return radical_ambient

    Gram_sub = restrict_gram(M, B_rows)
    planes = []
    while True:
        if B_rows.nrows() == 0 or Gram_sub.nrows() == 0:
            break

        out = hyperbolic_fp(Gram_sub)
        if out is None:
            break

        v_local, u_local = out   # local coordinates (length = Gram_sub.nrows())
        v_amb_row = (matrix(F, [list(v_local)]) * B_rows)[0]
        u_amb_row = (matrix(F, [list(u_local)]) * B_rows)[0]
        v_amb = vector(F, list(v_amb_row))
        u_amb = vector(F, list(u_amb_row))

        # use matrix * vector (no .column())
        w1 = M * v_amb
        w2 = M * u_amb
        W = Matrix(F, [ list(w1), list(w2) ])
        K = W.right_kernel()
        if K.dimension() == 0:
            B_rows = Matrix(F, 0, n, [])
            Gram_sub = Matrix(F, 0, 0, [])
            planes.append((v_amb, u_amb))
            break

        K_basis_cols = K.basis()
        B_rows = Matrix(F, [ list(col) for col in K_basis_cols ])
        Gram_sub = restrict_gram(M, B_rows)
        planes.append((v_amb, u_amb))
        if verbose:
            # print("Split off plane. Remaining dim (complement) =", B_rows.nrows())
            pass

    isotropic_list = radical_ambient + [ pair[0] for pair in planes ]
    return isotropic_list

def char2_max_isotrop(M):
    F = M.base_ring()
    n = M.nrows()
    V = VectorSpace(F, n)
    R_rows, B_rows = radical_and_complement_rows_fp(M)
    if B_rows.nrows() == 0:
        # only radical present
        return V.subspace([ vector(F, list(r)) for r in R_rows.rows() ])

    Gram_sub = restrict_gram(M, B_rows)
    rows = list(B_rows.rows())   # list of ambient row-vectors
    r = len(rows)

    # find a row whose self-pairing in Gram_sub is nonzero
    done = False
    for i, _row in enumerate(rows):
        if Gram_sub[i, i] != 0:
            done = True
            rows[i], rows[-1] = rows[-1], rows[i]
            break

    if done:
        # rebuild B_rows and Gram_sub after the swap
        B_rows = Matrix(F, [ list(rv) for rv in rows ])
        Gram_sub = restrict_gram(M, B_rows)
        rows = list(B_rows.rows())

        # try to make all but last have zero self-pairing by adding last row
        for i in range(len(rows) - 1):
            Gram_sub = restrict_gram(M, B_rows)
            if Gram_sub[i, i] != 0:
                rows[i] = rows[i] + rows[-1]
                B_rows = Matrix(F, [ list(rv) for rv in rows ])

    # collect those rows whose self-pairing (in Gram_sub) is zero
    Gram_sub = restrict_gram(M, B_rows)
    works = []
    for i, row in enumerate(B_rows.rows()):
        if Gram_sub[i, i] == 0:
            works.append(vector(F, list(row)))

    # build subspace: radical + the "works" rows (ambient vectors)
    ambient_rows = [ vector(F, list(r)) for r in R_rows.rows() ] + works
    return ambient_rows

def L_perp_mod2_basis(G, w):
    n = G.nrows()
    w = vector(ZZ, w)
    a = G * w  
    a = [x%2 for x in a]
    vecs = []
    bad = []
    for i in range(n):
        if a[i] == 0:
            zero = [0] * n
            zero[i] = 1
            vecs.append(zero)
        else:
            bad.append(i)
    curr = [0] * n
    for i in range(len(bad)):
        curr[bad[i]] = 1
        if i%2 == 0:
            curr[bad[0]] = 2
        vecs.append(curr.copy())
        curr[bad[0]] = 1

    return vecs

def Z_span_basis(gens):
    n = gens[0].degree()
    M = matrix(QQ, n, len(gens), gens) 
    den = lcm([c.denominator() for c in M.list()])
    M_int = (den * M).change_ring(ZZ)  
    H, U = M_int.hermite_form(transformation=True)

    cols = [H.column(j) for j in range(H.ncols()) if H.column(j) != 0]
    B_int = matrix(ZZ, cols)         

    B = (QQ(1)/den) * B_int
    return B


def p_neighbor_lattice(L_in, w, p=2):
    G = L_in.gram_matrix()

    perp_basis = L_perp_mod2_basis(G, w)    

    gens = [vector(QQ, w) / p] + [vector(QQ, v) for v in perp_basis]
    # B = Z_span_basis(gens)
    mat = Matrix(gens)
    int_mat = mat.denominator() * mat
    int_mat = int_mat.change_ring(ZZ)
    hnf_int = int_mat.hermite_form(include_zero_rows=False)
    B = hnf_int / mat.denominator()
    Gprime = B * G * B.transpose()

    return IntegralLattice(Gprime)

def even_sublattice(L):
    G = L.gram_matrix()
    n = G.nrows()
    d = vector(ZZ, G.diagonal()) % 2
    if d.is_zero():
        return L
    pivot = []
    basis = []
    for i in range(n):
        if d[i] == 1:
            pivot.append(i)
        else:
            v = [0] * n
            v[i] = 1
            basis.append(v)
    v = [0]*n
    v[pivot[0]] = 2
    basis.append(v.copy())
    for i in range(1,len(pivot)):
        v[pivot[i]] = 1
        v[pivot[0]] = 3 - v[pivot[0]]
        basis.append(v.copy())
    B = Matrix(ZZ, basis)
    B = B * L.basis_matrix()
    # print(B)
    #return [IntegralLattice(B * L.gram_matrix() * B.transpose()), B]
    return L.sublattice(B)

# ------------------------
# Integer kernel basis for B v == 0 (mod 2), and finishing logic
# ------------------------

def integer_basis(B):
    B = Matrix(ZZ, B)   
    n = B.ncols()
    B2 = B.change_ring(GF(2))
    K = B2.right_kernel()
    basis_gf2 = K.basis()   
    lifted = []
    for vec in basis_gf2:
        lifted.append(vector(ZZ, [int(vec[j]) for j in range(n)]))

    two_std = [2 * vector(ZZ, [1 if i == j else 0 for j in range(n)]) for i in range(n)]

    Free = ZZ**n       
    Ssub = Free.submodule(lifted + two_std)
    zbasis = Ssub.basis()  

    return zbasis

def fnd(L):
    B = L.basis_matrix()
    G = L.gram_matrix()
    # zbasis = integer_basis((B*G)%2)
    # zbasis = integer_basis(G%2)
    for v in list(itertools.product(range(8), repeat=min(len(G.rows()),5))):
        prim = False
        vv = []
        for i in range(len(v)): 
            vv.append(Integer(v[i]))
        while len(vv) < len(G.rows()):
            vv.append(0)
        vv = vector(ZZ, vv)
        # print("vv", vv)
        #res = [0]*len(G.rows())
        #res = vector(res)
        #for i in range(len(G.rows())):
            # res += vector(zbasis[i] * vv[i])
        #    res += vector(vv[i])
        for val in vv:#res:
            if val%2==1:
                prim=True
        if prim==False:
            continue
        if (vv*G * vv.column())[0] % 8==0:
            return vv # * L.basis_matrix()
    
    return -1

def finish(L):
    evenL = even_sublattice(L)

    print(evenL)
    if L==evenL:
        return L
    assert (L / evenL).cardinality() == 2
    v = fnd(L)
    if v == -1:
        return evenL
    else:
        print("lol")
        return p_neighbor_lattice(L,v)

# ------------------------
# Helpers for reducing rationals mod p and building p*M^{-1} over F_p
# ------------------------

def _Q_to_Fp_entry(r, p):
    r = QQ(r)
    if r == 0:
        return GF(p)(0)
    a = ZZ(r.numerator())
    b = ZZ(r.denominator())
    va = a.valuation(p) if a != 0 else +Infinity
    vb = b.valuation(p) if b != 0 else 0
    # cancel common p-powers
    t = min(va if va != +Infinity else va, vb)
    if t != +Infinity and t > 0:
        a //= (p**t)
        b //= (p**t)
        va -= t
        vb -= t
    # if denominator still has p, valuation(r) > 0, so 0 mod p
    if b.valuation(p) > 0:
        return GF(p)(0)
    return GF(p)(a % p) * GF(p)(Integer(b % p)).inverse()

def _matrix_Q_to_Fp(MQ, p):
    return matrix(GF(p), [[_Q_to_Fp_entry(MQ[i,j], p) for j in range(MQ.ncols())] for i in range(MQ.nrows())])


def is_overlattice(L1, L2):
    B1 = matrix(QQ, L1.basis())     
    B2 = matrix(QQ, L2.basis())

    coords = B2 * B1.inverse() 

    return all(c in ZZ for c in coords.list())

def maximal_overlattice_2(L_in, do_asserts=True):
    ogL = L_in
    L = L_in

    # Step 1: Z-saturate
    L_sat = algo3_8(L)
    # Step 2: Work prime-by-prime on the dual to adjoin isotropic classes from D(L)
    M = L_sat.gram_matrix()
    Minv = M.inverse()   # over QQ
    detM = Integer(M.determinant())
    ps = detM.prime_factors()
    if 2 not in ps:
        ps.append(2)

    to_adjoin = []

    for p in ps:
        # quadratic form on the p-primary discriminant: use Gram p*M^{-1} mod p
        Mp_dual = _matrix_Q_to_Fp(p*Minv, p)

        if p == 2:
            iso_basis = char2_max_isotrop(Mp_dual)
            # char2_max_isotrop may return a list of vectors (ambient rows)
            if hasattr(iso_basis, 'basis'):
                iso_list = iso_basis.basis()
            else:
                iso_list = iso_basis
            Fp = GF(p)
            for v in iso_list:
                vZ = vector(ZZ, [int(Fp(x)) for x in v])   # 0/1 reps
                v_dual = vector(QQ, vZ) * Minv            # in L*
                q = (v_dual * M * v_dual.column())[0]
                if q in ZZ:
                    to_adjoin.append(v_dual*L_sat.basis_matrix())
        else:
            iso_basis = max_isotrop_fp(Mp_dual, verbose=False)  # list of row vectors over F_p
            Fp = GF(p)
            for v in iso_basis:
                vZ = vector(ZZ, [int(Fp(x)) for x in v])  # 0..p-1 reps
                v_dual = vector(QQ, vZ) * Minv            # in L*
                q = (v_dual * M * v_dual.column())[0]
                if q in ZZ:
                    to_adjoin.append(v_dual*L_sat.basis_matrix())

    if to_adjoin:
        L_sat = L_sat.overlattice(list(L_sat.basis()) + to_adjoin)
        M = L_sat.gram_matrix()

    L_sat = finish(L_sat)
    if do_asserts:
        L_sat_max = L_sat.maximal_overlattice()
        print(L_sat_max, "actual max")
        print(L_sat_max.gram_matrix())
        #assert L_sat == L_sat_max
        #assert is_overlattice(L_sat, ogL)

    return L_sat

#L = IntegralLattice(Matrix(QQ, [[4,0,0,0,0], [0,4,0,0,0], [0,0,8,0,0], [0,0,0,4,0], [0,0,0,0,8]]))
#L_max = maximal_overlattice_2(L)
#print(L_max)
#print(L_max.gram_matrix())

"""
[1/2   0   0 1/2   0]
[  0 1/2   0 1/2   0]
[  0   0 1/4 1/2 1/4]
[  0   0   0   1   0]
[  0   0   0   0 1/2]

this is the sage code basis, the gram is the smae
"""
