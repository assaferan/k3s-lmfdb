n  = int(input())
V = VectorSpace(QQ, n)

q = int(input())
F = GF(q)

def ftoq(x, F):
    return Integer(x.lift())

def B_mod(u, v, B):
    return F(B(u,v))

def is_square_mod(x, F):
    return x.is_square()

def solve_quadratic_mod(a2, a1, a0, F):
    """
    Solve the quadratic equation a2*t^2 + a1*t + a0 = 0 in F.
    char(F) != 2.
    """
    if a2 != 0:
        disc = a1**2 - 4*a2*a0
        if not is_square_mod(disc, F):
            return None
        sqrt_disc = disc.sqrt()
        sol1 = (-a1 + sqrt_disc) / (2 * a2)
        sol2 = (-a1 - sqrt_disc) / (2 * a2)
        return [sol1, sol2]
    else:
        # Linear equation: a1*t + a0 = 0.
        if a1 != 0:
            return [-a0 / a1]
        else:
            return [F(0)] if a0 == 0 else None

def find_isotropic(V, B, F, trials=50):

    for i in range(trials):
        a = V.random_element()
        m = V.random_element()
        if a.is_zero() or m.is_zero():
            continue
        if a in V.span([m]):
            continue
        A0 = B_mod(a, a, B)
        A1 = 2 * B_mod(a, m, B)
        A2 = B_mod(m, m, B)
        sols = solve_quadratic_mod(A2, A1, A0, F)
        if sols is not None:
            t = sols[0]
            t_Q = ftoq(t, F) 
            v = a + t_Q * m
            if not v.is_zero() and B_mod(v, v, B) == 0:
                return v
    return None

def compute_radical(V, B, F):
    basis = V.basis()
    n = V.dimension()
    M = matrix(F, n, n, [B_mod(u, v, B) for u in basis for v in basis])
    ker = M.right_kernel()
    rad_vecs = []
    for vec in ker.basis():
        lifted_coords = [ftoq(x, F) for x in vec]
        rad_vecs.append(sum(c*v for c, v in zip(lifted_coords, basis)))
    return V.subspace(rad_vecs)

def complement_subspace(V, U):
    U_basis = U.basis()
    W_basis = V.linear_extension(U_basis).complement().basis()
    return V.subspace(W_basis)

def mod_orthogonal_complement(V, U, B, F):
    V_basis = V.basis()
    U_basis = U.basis()
    n = len(V_basis)
    m = len(U_basis)
    A = matrix(F, m, n, [[B_mod(b, u, B) for b in V_basis] for u in U_basis])
    ker = A.right_kernel()
    lifted_basis = []
    for vec in ker.basis():
        lifted_coords = [ftoq(x, F) for x in vec]
        lifted_basis.append(V(lifted_coords))
    return V.subspace(lifted_basis)

def hyper_plane(v, V, B, F):

    for w in V.basis():
        if B_mod(v, w, B) != 0:
            inv_factor = 1 / B_mod(v, w, B)
            inv_factor_Q = ftoq(inv_factor, F)
            w = inv_factor_Q * w
            correction = ftoq(B_mod(w, v, B), F)
            w = w - correction * v
            return V.subspace([v, w])
def decompose_bilinear_form(V, B, F):
    R = compute_radical(V, B, F)
    if R.dimension() > 0:
        V0 = complement_subspace(V, R)
    else:
        V0 = V
    
    hyperbolic_planes = []
    V_current = V0
    while True:
        d = V_current.dimension()
        if d <= 1:
            break
        if d == 2:
            basis = V_current.basis()
            M = matrix(F, 2, 2, [B_mod(u,v, B) for u in basis for v in basis])
            if not is_square_mod(-M.determinant(), F):
                break
        v = find_isotropic(V_current, B, F)
        if v is None:
            break
        try:
            H_plane = hyper_plane(v, V_current, B, F)
        except ValueError:
            break
        hyperbolic_planes.append(H_plane)
        V_current = mod_orthogonal_complement(V_current, H_plane, B, F)
    
    if hyperbolic_planes:
        H_total = hyperbolic_planes[0]
        for H in hyperbolic_planes[1:]:
            H_total = H_total.direct_sum(H)[0]
    else:
        H_total = V.subspace([]) 
    return {R, H_total, V_current}

M = []
for i in range(n):
    arr = [float(x) for x in input().split()]
    M.append(arr)
def B(u, v):
    return u * (M * v)

decomp = decompose_bilinear_form(V, B, F)
print(decomp)