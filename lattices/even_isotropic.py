def compute_radical(V, B):
    basis = V.basis()
    n = V.dimension()
    M = matrix(GF(2), n, n, [B(u, v) for u in basis for v in basis])
    ker = M.right_kernel()
    rad_vecs = []
    for vec in ker.basis():
        rad_vec = sum(c * v for c, v in zip(vec, basis))
        rad_vecs.append(rad_vec)
    return V.subspace(rad_vecs)

def complement_subspace(V, U):
    U_basis = U.basis()
    W_basis = V.linear_extension(U_basis).complement().basis()
    return V.subspace(W_basis)

def decompose_bilinear_form(V, B, Q):
    R = compute_radical(V, B)
    if R.dimension() > 0:
        Vp = complement_subspace(V, R)
    else:
        Vp = V
    basis_Vp = Vp.basis()
    nonz = None
    for x in basis_Vp:
        if Q(x) != 0: 
            nonz = x
            break

    if nonz is None:
        I = Vp
        A = V.subspace([])
    else:
        A = Vp.subspace([nonz])
        new_basis = []
        for y in basis_Vp:
            if y == nonz:
                continue
            if Q(y) != 0:
                y_new = y + nonz
            else:
                y_new = y
            new_basis.append(y_new)
        I = Vp.subspace(new_basis)
    return {"radical": R, "isotropic": I, "anisotropic": A}

