// Automorphism groups through the root system, after Chenevier, "Unimodular
// hunting" (arXiv:2410.18788), Remark 4.4 and Definition 4.5.
//
// Let R be the vectors of norm 1 and 2 in a positive definite integral lattice L.
// Their reflections x -> x - 2 (x.v)/(v.v) v preserve L, R is a reduced root
// system, and Aut(L) permutes R, so the Weyl group W = W(R) is normal in Aut(L).
// W acts simply transitively on the Weyl chambers of R, hence
//     Aut(L) = W x| Stab(C) = W x| Stab(rho),
// where rho is the sum of the positive roots of a chamber C.  Plesken-Souvignier
// on G together with a form built from G rho computes Stab(+-rho), which contains
// -1 (it swaps rho and -rho), so |Aut(L)| = |W| * |Stab(+-rho)| / 2.  When L has
// a large root system, Stab(+-rho) is tiny and the expensive search shrinks.

declare verbose AutWeyl, 1;
declare attributes Lat : WeylForms;

// coordinates of the roots of L (vectors of norm 1 or 2), both signs
function lattice_roots(L)
    return &cat[[c, -c] where c := Vector(Integers(), Coordinates(x[1])) : x in ShortVectors(L, 2)];
end function;

// rho, the sum of the positive roots for a random generic functional, and the
// form F = 2G + u u^T with u = G rho made primitive.  The isometries of G that
// preserve F are Stab(+-rho).  F goes first in Plesken-Souvignier, which
// enumerates the short vectors of the first form: under F the vectors with a
// large component along rho are no longer short.  On a rank-16 lattice with
// roots D14 A1 this took 0.4 s, against 12.6 s with G first.  (The rank-one
// form u u^T alone is equivalent, but Magma does not return on it: E8 ran over
// 5 min.)
function rho_form(G, roots)
    n := Nrows(G);
    repeat
        f := Vector(Integers(), [Random(-10^6, 10^6) : i in [1..n]]);
    until forall{r : r in roots | (r, f) ne 0};
    pos := [r : r in roots | (r, f) gt 0];
    rho := &+pos;
    grho := rho * G;
    u := grho div GCD(Eltseq(grho));
    return 2 * G + Matrix(Integers(), n, n, [u[i] * u[j] : i, j in [1..n]]), pos;
end function;

intrinsic AutomorphismGroupWeyl(L::Lat) -> GrpMat
{The automorphism group of the positive definite integral lattice L, computed as
W(R) x| Stab(rho) for the root system R of vectors of norm 1 and 2.  The group is
in the coordinates of L's basis (the frame of AutomorphismGroup(L)) and carries its
order, so #A costs nothing.}
    n := Rank(L);
    G := ChangeRing(GramMatrix(L), Integers());
    roots := lattice_roots(L);
    if #roots eq 0 then
        return AutomorphismGroup(L);
    end if;
    dot := func<u, v | (u * G, v)>;

    // positive roots: those on the positive side of a generic linear functional
    F, pos := rho_form(G, roots);
    posset := Set(pos);
    // simple roots: the positive roots that are not a sum of two positive roots
    simple := [r : r in pos | not exists{u : u in pos | r - u in posset}];

    // |W| from the Cartan matrix of the simple roots
    C := Matrix(Integers(), #simple, #simple,
                [2 * dot(a, b) div dot(b, b) : a, b in simple]);
    W_order := CoxeterGroupOrder(C);

    // Stab(+-rho): see rho_form
    S := AutomorphismGroup(LatticeWithGram(F), [G]);

    // reflections in the simple roots, acting on row coordinate vectors
    GLn := GL(n, Integers());
    refl := [GLn | IdentityMatrix(Integers(), n) -
             Matrix(Integers(), n, 1, Eltseq((2 div dot(a, a)) * (a * G))) *
             Matrix(Integers(), 1, n, Eltseq(a)) : a in simple];
    A := sub<GLn | refl cat [GLn | g : g in Generators(S)]>;
    AssertAttribute(A, "Order", W_order * #S div 2);
    vprintf AutWeyl: "roots %o, simple %o (%o), |W| = %o, |Stab(+-rho)| = %o\n",
        #roots, #simple, CartanName(C), W_order, #S;
    return A;
end intrinsic;

// <k, M, number of roots of M, G, F> for L, cached on L.  L = Z^k + M with Z^k
// the span of the vectors of norm 1: in an integral lattice two of them are
// orthogonal or equal up to sign, and x - (x, e) e is in L for each of them, so
// they split off orthogonally.  G is the Gram matrix of M (LLL-reduced) and F
// its form from rho_form, or G when M has no roots.
function weyl_forms(L)
    if not assigned L`WeylForms then
        ones := [x[1] : x in ShortVectors(L, 1, 1)];
        if #ones eq 0 then
            k := 0; M := L;
        else
            E := sub<L | ones>;
            k := Rank(E);
            M := OrthogonalComplementFaster(L, E);
        end if;
        G := Rank(M) eq 0 select ZeroMatrix(Integers(), 0, 0)
             else LLLGram(ChangeRing(GramMatrix(M), Integers()));
        M := LatticeWithGram(G);
        roots := Rank(M) eq 0 select [] else lattice_roots(M);
        L`WeylForms := <k, M, #roots, G, #roots eq 0 select G else rho_form(G, roots)>;
    end if;
    return L`WeylForms;
end function;

intrinsic IsIsometricWeyl(L1::Lat, L2::Lat) -> BoolElt
{Whether L1 and L2 are isometric, computed up to the Weyl group of their roots
(vectors of norm 1 and 2).  First L_i = Z^k_i + M_i, with Z^k_i the span of the
vectors of norm 1, so L1 and L2 are isometric exactly when k_1 = k_2 and M_1 and
M_2 are.  An isometry carries a Weyl chamber of M_1 to one of M_2, and W(R2) is
transitive on those, so M_1 and M_2 are isometric exactly when some isometry
carries rho_1 to rho_2; Plesken-Souvignier on F_i = 2G_i + u_i u_i^T, with G_i
as extra form, decides that.  The forms are cached on the lattices, so testing
one lattice against many costs one form each.  Without roots this is
IsIsometric(M_1, M_2).}
    w1 := weyl_forms(L1); w2 := weyl_forms(L2);
    if w1[1] ne w2[1] or w1[3] ne w2[3] then return false; end if;
    // splitting off Z^k first matters: a lattice Z^15 + (rank 1) took 38 s
    // without it, as the rho of the type-B roots of Z^k is a poor guide
    if Rank(w1[2]) eq 0 then return true; end if;
    if w1[3] eq 0 then return IsIsometric(w1[2], w2[2]); end if;
    S := [PowerSet(Parent(w1[4])) | ];
    return IsIsometric(LatticeWithGram(w1[5]), [w1[4]], S, LatticeWithGram(w2[5]), [w2[4]], S);
end intrinsic;
