// The p-neighbour adjacency (Hecke) matrix of a genus, from its representatives.
//
// For each representative L the p-neighbours come from the lines of L/pL, one per
// orbit of Aut(L); an automorphism carries the neighbours of one line to those of
// another, so each orbit adds its size to the classes of its neighbours.  Each
// neighbour is matched to a representative by cheap invariants, then by
// IsIsometricWeyl.
//
// This replaces Magma's AdjacencyMatrix, which returns the zero matrix for every
// odd genus at p = 2 (Magma-Maths/Magma#496).  For p = 2 and L odd, a line <v>
// with v.v = 0 mod 4, v not in the radical of L/2L, has two neighbours
// {x in L : (x, v) even} + Z w/2, for the lifts w = v and w = v + 2b with (v, b)
// odd.  Magma's Neighbor refuses these when det(L) is even, so they are built
// directly.

import !"/Lattice/Lat/neighbors.m" : Adjust, IsNonsingularVector;

// the 2-neighbour {x in L : (x, w) even} + Z w/2 of L, with Gram matrix G,
// at the coordinate vector c of w
function two_neighbour(G, c)
    n := Nrows(G);
    K := Kernel(Matrix(GF(2), n, 1, Eltseq(c * G)));
    Lw := Matrix(Integers(), [Eltseq(ChangeRing(b, Integers())) : b in Basis(K)] cat
                             [Eltseq(2 * x) : x in Rows(IdentityMatrix(Integers(), n))]);
    H := HermiteForm(VerticalJoin(2 * Lw, Matrix(Integers(), 1, n, Eltseq(c))));
    B := ChangeRing(Submatrix(H, 1, 1, n, n), Rationals()) / 2;
    return LatticeWithGram(ChangeRing(B * ChangeRing(G, Rationals()) * Transpose(B), Integers()));
end function;

// the norm mod 8 of a characteristic vector of the lattice with Gram matrix G,
// det G odd: its oddity (van der Blij)
function char_norm_mod8(G)
    d := Vector(GF(2), [G[i, i] : i in [1..Nrows(G)]]);
    w := ChangeRing(Solution(ChangeRing(G, GF(2)), d), Integers());
    return InnerProduct(w * G, w) mod 8;
end function;

intrinsic NeighbourAdjacencyMatrix(reps::SeqEnum, p::RngIntElt) -> AlgMatElt
{The p-neighbour adjacency matrix of the genus with the complete list of class
representatives reps, in the orientation of Magma's AdjacencyMatrix: entry
[i, j] is the number of p-neighbours of reps[j] isometric to reps[i].  Unlike
AdjacencyMatrix, it is correct for odd genera at p = 2.}
    require #reps gt 0 and forall{L : L in reps | Type(L) eq Lat} :
        "Argument 1 must be a nonempty sequence of lattices";
    require IsPrime(p) : "Argument 2 must be prime";
    h := #reps;
    n := Rank(reps[1]);
    Z := Integers();
    // work with primitive integral Gram matrices: scaling does not change neighbours
    grams := [ChangeRing(GramMatrix(L), Z) : L in reps];
    c := GCD(Eltseq(grams[1]));
    reps := [LatticeWithGram(g div c) : g in grams];
    if n le 2 then
        G := Genus(reps[1]);
        G`Representatives := reps; G`IsNatural := true;
        return AdjacencyMatrix(G, p);
    end if;

    odd2 := p eq 2 and not IsEven(reps[1]);
    // A p-neighbour has the same det and the same completions away from p, so it
    // is in the genus exactly when its p-adic genus is.  At p not dividing 2 det
    // that always holds.  At p = 2 the parity must match, and when det is odd
    // the 2-adic genus is fixed by rank, det, parity and oddity.
    G1 := ChangeRing(GramMatrix(reps[1]), Z);
    det_odd := IsOdd(Determinant(G1));
    check_genus := p eq 2 or Determinant(G1) mod p eq 0;
    LG := check_genus select LocalGenus(reps[1], p) else 0;
    oddity := (p eq 2 and odd2 and det_odd) select char_norm_mod8(G1) else 0;
    function in_genus(N)
        if not check_genus then return true; end if;
        if p eq 2 then
            if IsEven(N) ne not odd2 then return false; end if;
            if det_odd then
                return not odd2 or char_norm_mod8(ChangeRing(GramMatrix(N), Z)) eq oddity;
            end if;
        end if;
        return LocalGenus(N, p) eq LG;
    end function;
    inv := func<L | [#ShortVectors(L, k, k) : k in [1..3]]>;
    rinv := [inv(L) : L in reps];

    function classify(N)
        N := LatticeWithGram(LLLGram(ChangeRing(GramMatrix(N), Z)));
        iv := inv(N);
        cand := [j : j in [1..h] | rinv[j] eq iv];
        error if #cand eq 0, "a neighbour matches no representative: reps is not complete";
        for k in [1..#cand - 1] do
            if IsIsometricWeyl(N, reps[cand[k]]) then return cand[k]; end if;
        end for;
        return cand[#cand];
    end function;

    A := ZeroMatrix(Z, h, h);
    for i in [1..h] do
        L := reps[i];
        G := ChangeRing(GramMatrix(L), Z);
        singular := Determinant(G) mod p eq 0;
        O := LineOrbits(ChangeRing(AutomorphismGroupFaster(L), GF(p)));
        for o in O do
            v := L ! ChangeRing(o[1].1, Z);
            if odd2 then
                if Norm(v) mod 4 ne 0 then continue; end if;
                B := [x : x in Basis(L) | (v, x) mod 2 eq 1];
                if #B eq 0 then continue; end if;   // v in the radical of L/2L
                nbs := [two_neighbour(G, Vector(Z, Coordinates(w))) : w in [v, v + 2 * B[1]]];
            else
                w := Adjust(v, p);
                if IsZero(w) or (singular and not IsNonsingularVector(w, p)) then continue; end if;
                nbs := [Neighbor(L, w, p)];
            end if;
            for N in nbs do
                if in_genus(N) then
                    j := classify(N);
                    A[i, j] +:= #o;
                end if;
            end for;
        end for;
    end for;
    return MatrixAlgebra(Z, h) ! Transpose(A);
end intrinsic;
