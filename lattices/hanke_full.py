# Put this in a Sage session (expects `from sage.all import *`).
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

def mp_comp(L):
    m_p = {}
    gen = L.genus()
    for local in gen.local_symbols():
        m_p[local.prime()] = local._symbol[-1][0]
    return m_p

def zsat(L, max_iters=200, verbose=True):
    n = L.rank()
    pv = mp_comp(L)
    if verbose:
        print("initial p-vals (m_p):", pv)

    for it in range(1, max_iters+1):
        if verbose:
            print("iter", it)
            print(" Gram (QQ) =\n", L.gram_matrix())
            print(" m_p (old) =", pv)
        bad = {p: e for p, e in pv.items() if e >= 2}
        if not bad:
            print("FINAL", L)
            return L
        cst = ZZ(1)
        for p, e in pv.items():
            cst *= ZZ(p) ** ZZ((e + 1)//2)
        L  = L.overlattice((cst * L.dual_lattice()).basis())
        pv = mp_comp(L)
    return L

def B(v, M, w=None):
    rng = M.base_ring()
    try:
        v = vector(rng, [rng(a) for a in v])
    except:
        print(v)
    if w != None:
        try:
            w = vector(rng, [rng(a) for a in w])
        except:
            print(w)
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
    FIXED: ensure we pass lists of scalars to Matrix(...) instead of vector objects.
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
    # store columns as lists of scalars (so matrix constructor sees scalars only)
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
            print("Split off plane. Remaining dim (complement) =", B_rows.nrows())

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

def is_even(G):
    return all((Integer(G[i,i]) % 2) == 0 for i in range(G.nrows()))

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
            zero[i] = 2
            vecs.append(zero)
        else:
            bad.append(i)
    curr = [0] * n
    for i in range(len(bad)):
        curr[bad[i]] = 2
        if i%2 == 0:
            curr[bad[0]] = 4
        vecs.append(curr.copy())
        curr[bad[0]] = 2

    return vecs
def p_neighbor_lattice(L_in, w):
    G = L_in.gram_matrix()
    gens_q = [w] + L_perp_mod2_basis(G, w)
    Mamb = FreeModule(ZZ,L_in.rank())
    Lpr = Mamb.submodule([vector(v) for v in gens_q])
    B = Lpr.basis_matrix()
    print(B)
    Gprime_int = (B.transpose() * G * B)/4
    print(Gprime_int)
    return IntegralLattice(Gprime_int)


def even_sublattice(L):
    G = L.gram_matrix()
    n = G.nrows()
    d = vector(ZZ, G.diagonal()) % 2
    print(d)
    if d.is_zero():
        return [L,[[1 if i==j else 0 for j in range(0, n)] for i in range(n)]]
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
    basis.append(v)
    for i in range(1,len(pivot)):
        v[pivot[i]] = 1
        v[pivot[0]] = 3 - v[pivot[0]]
        basis.append(v)
        w = Matrix(n,1, v)
        print(w.transpose() * G * w)
    
    B = Matrix(ZZ, basis)
    print(B)
    return [IntegralLattice(B * L.gram_matrix() * B.transpose()), B]

# SageMath code: integer Z-basis for solutions of B v == 0 (mod 2)

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

def fnd(G, B):
    zbasis = integer_basis((B*G)%2)
    for v in list(itertools.product(range(8), repeat=min(len(G.rows()),5))):
        prim = False
        vv = []
        for i in range(len(v)): 
            vv.append(Integer(v[i]))
        while len(vv) < len(G.rows()):
            vv.append(0)
        res = [0]*len(G.rows())
        res = vector(res)
        for i in range(len(G.rows())):
            res += vector(zbasis[i] * vv[i])
        for val in res:
            if val%2==1:
                prim=True
        if prim==False:
            continue
        if (res*G * res.column())[0] % 8==0:
            return res
    
    return -1
def finish(L):
    ret = even_sublattice(L)
    evenL = ret[0]
    print("--EVEN LATTICE--")
    print(evenL)
    if L==evenL:
        return L
    v = fnd(L.gram_matrix(), ret[1])
    print("--VECTOR FOUND--")
    print(v)
    if v == -1:
        print("hi")
        return evenL
    else:
        return p_neighbor_lattice(L,v)

A = Matrix(QQ, [[22,1,3],[1,4,7],[3,7,12]])   # symmetric rational matrix
V = VectorSpace(QQ,3)
L = IntegralLattice(A)
L_sat = zsat(L, max_iters=500, verbose=True)
B_basis = L_sat.basis()
print("\n=== FINISHED SATURATION ===")

print("IntegralLattice Gram:", L_sat.gram_matrix())
print("B (row-basis used):\n", B_basis)

# Now test maximal isotropic over finite fields using the field-aware routines
M = L_sat.gram_matrix()
ps = Integer(M.determinant()).prime_factors()
if 2 not in ps:
    ps.append(2)

zs = [0]*len(ps)

isotrop = []
for k,p in enumerate(ps):
    print("\n--- working over GF(%s) ---" % p)
    Mp = matrix(GF(p), M)
    if p == 2:
        iso2 = char2_max_isotrop(Mp)
        print("char2_max_isotrop_fp returned %d vectors:" % len(iso2))
        for i, v in enumerate(iso2):
            print(" v[%d] =" % i, v)
            lft = vector(ZZ, [int(a) for a in v])
            for j,elem in enumerate(lft):
                zs[k] = Integer(elem)
                lft[j] = find_min_x(ps, zs)
                zs[k] = 0
            isotrop.append(lft)
    else:
        isp = max_isotrop_fp(Mp, verbose=True)
        print("max_isotrop_fp returned %d vectors:" % len(isp))
        for i, v in enumerate(isp):
            print(" v[%d] =" % i, v)
            lft = vector(ZZ, [int(a) for a in v])
            for j,elem in enumerate(lft):
                zs[k] = Integer(elem)
                lft[j] = find_min_x(ps, zs)
                zs[k] = 0
            isotrop.append(lft)
L_sat = L_sat.overlattice(isotrop)
M= L_sat.gram_matrix()

print("\n=== AFTER ISOTROPIC ===")


print(L_sat)
L_sat = finish(L_sat)
print(L_sat)
L_sat_max = L_sat.maximal_overlattice() 
print(L_sat_max)
if L_sat != L_sat_max:
    print('incorrect')

print("\nDone.")
