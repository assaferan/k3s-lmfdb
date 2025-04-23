    def _saturate(self):
        L = self
        while True:
            B = L.gram_matrix()
            disc = B.det().numerator()
            exp = {}
            for p in primes(1, abs(disc)):
                if disc % p != 0:
                    continue
                i = 0
                while any((v*B*v).valuation(p) >= i for v in L.basis()):
                    i += 1
                m = i - 1
                if m > 0:
                    exp[p] = (m + 1)//2
            if not exp:
                return L
            dual = L.dual_lattice().basis()
            gens = list(L.basis())
            for p, e in exp.items():
                for v in dual:
                    gens.append((p**e)*v)
            L = L.overlattice(gens)

    def _max_iso(self, D, p):
        F = D.base_ring()
        V = VectorSpace(F, D.nrows())
        B = lambda u, v: u*D*v
        Q = lambda u: B(u, u)
        if p != 2:
            if V.dimension() == 1:
                return []
            if V.dimension() == 2 and kronecker_symbol(-int(D.det()), p) == -1:
                return []
            U = V.subspace([])
            W = V
            while W.dimension() >= 2:
                v = None
                for _ in range(20):
                    a, b = W.random_element(), W.random_element()
                    A = B(b, b); C = B(a, a); E = 2*B(a, b)
                    if A == 0:
                        continue
                    disc = E^2 - 4*A*C
                    if not disc.is_square():
                        continue
                    t = (-E + disc.sqrt())/(2*A)
                    v0 = a + t*b
                    if v0 != 0:
                        v = v0
                        break
                if v is None:
                    break
                for w0 in W.basis():
                    if B(v, w0) != 0:
                        w = w0/B(v, w0)
                        w = w - (B(w, w)/2)*v
                        break
                U = U + V.subspace([v])
                W = W.intersection(V.orthogonal_complement([v, w], form=D))
            return U.basis()
        R = matrix(D).left_kernel().basis()
        Rsub = V.subspace(R)
        std = [V.unit_vector(i) for i in range(V.dimension())]
        Vp = [e for e in std if not Rsub.contains(e)]
        idx = next((i for i, v in enumerate(Vp) if Q(v) != 0), None)
        if idx is not None:
            Vp[idx], Vp[-1] = Vp[-1], Vp[idx]
        if Q(Vp[-1]) != 0:
            vn = Vp[-1]
            I = []
            for v in Vp[:-1]:
                I.append(v if Q(v) == 0 else v + vn)
        else:
            I = Vp
        return I

    def _even_sublattice(self, p=2):
        B = self.gram_matrix()
        evens = [v for v in self.basis() if (v*B*v) % p == 0]
        return self.sublattice(evens)

    def maximal_overlattice(self, p=None):
        try:
            Q = self.quadratic_form()
        except AttributeError:
            L0 = self
        else:
            H = (Q.matrix() + Q.matrix().transpose())//2
            L0 = self.ambient_module().span(self.basis(), bilinear_form=H)
        if p is None:
            disc = L0.gram_matrix().det().numerator()
            S = [q for q in primes(1, abs(disc)) if disc % q == 0]
        else:
            S = [p]
        Ls = L0._saturate()
        gens = list(Ls.basis())
        if S:
            B = Ls.gram_matrix()
            Binv = B.inverse()
            dual = [sum(Binv[i, j]*Ls.basis()[j] for j in range(B.ncols()))
                    for i in range(B.ncols())]
            Pbig = prod(S) if p is None else 1
            for q in S:
                D = matrix(GF(q), len(dual))
                for i, u in enumerate(dual):
                    for j, v in enumerate(dual):
                        D[i, j] = ((u*B*v)//q) % q
                U = self._max_iso(D, q)
                Mq = (Pbig//q) if p is None else 1
                for vbar in U:
                    v = sum(vbar[i]*dual[i] for i in range(len(dual)))
                    gens.append(Mq*v)
        L1 = Ls.overlattice(gens)
        L1 = L1._saturate()
        if hasattr(self, 'quadratic_form') and (p is None or p == 2):
            while not L1.is_even():
                Qnbrs = L1.quadratic_form().neighbor_iteration([L1.quadratic_form()], 2)
                Lnbrs = [IntegralLattice(q.matrix()) for q in Qnbrs]
                for N in Lnbrs:
                    if N.is_even():
                        L1 = N
                        break
                else:
                    L1 = L1._even_sublattice(2)
        return L1
