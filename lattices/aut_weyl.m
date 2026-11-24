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

// coordinates of the roots of L (vectors of norm 1 or 2), both signs
function lattice_roots(L)
    return &cat[[c, -c] where c := Vector(Integers(), Coordinates(x[1])) : x in ShortVectors(L, 2)];
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
    repeat
        f := Vector(Integers(), [Random(-10^6, 10^6) : i in [1..n]]);
    until forall{r : r in roots | (r, f) ne 0};
    pos := [r : r in roots | (r, f) gt 0];
    posset := Set(pos);
    // simple roots: the positive roots that are not a sum of two positive roots
    simple := [r : r in pos | not exists{u : u in pos | r - u in posset}];
    rho := &+pos;

    // |W| from the Cartan matrix of the simple roots
    C := Matrix(Integers(), #simple, #simple,
                [2 * dot(a, b) div dot(b, b) : a, b in simple]);
    W_order := CoxeterGroupOrder(C);

    // Stab(+-rho) as the isometries of G that also preserve F = 2G + u u^T, with
    // u = G rho divided by its content.  F goes first: Plesken-Souvignier
    // enumerates the short vectors of the first form, and under F the vectors
    // with a large component along rho are no longer short.  On a rank-16
    // lattice with roots D14 A1 this took 0.4 s, against 12.6 s with G first.
    // (The rank-one form u u^T alone is equivalent but Magma does not return on
    // it: E8 ran > 5 min.)
    grho := rho * G;
    u := grho div GCD(Eltseq(grho));
    F := 2 * G + Matrix(Integers(), n, n, [u[i] * u[j] : i, j in [1..n]]);
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
