// Theta series of positive definite lattices by gluing orthogonal blocks.
//
// Magma's ThetaSeries enumerates every vector of L up to the requested norm,
// about V_n N^(n/2) / sqrt(det L) of them; at rank 10-12 and N = 150 that is
// 10^10 to 10^13 vectors, so the fill stage never reached its target precision.
//
// Split L (in an LLL-reduced basis e_1..e_n) into mutually orthogonal blocks
// A_1, ..., A_m: A_t is the orthogonal complement of e_1..e_(s_(t-1)) inside the
// span of e_1..e_(s_t).  Let P_t be the orthogonal projection of L to A_t (x) Q.
// Every x in L is a sum of its projections a_t in P_t, |x|^2 = sum |a_t|^2, and
// conversely a sum of a_t in P_t is in L exactly when the tuple of classes
// (a_t + A_t) lies in the image H of L in the product of the P_t/A_t.  Hence
//     theta_L = sum_(h in H) prod_t theta_(A_t + h_t),
// and each coset theta needs only the vectors of a lattice of rank <= BlockRank.

declare verbose ThetaGlue, 1;

// Coset theta series of X + r for norms <= N.  The coset lies in the dual of X
// (r is the projection of a vector of L, and X is in L), so every norm in it is
// |r|^2 mod 1: the series is q^off * sum_k counts[k+1] q^k with off the
// fractional part of |r|^2.  CloseVectors returns every x in X (0 and both
// signs) with |x + r|^2 in the given range.  The norm range is cut into slices
// holding a bounded number of vectors, so memory stays bounded however large N is.
function coset_theta(X, r, N, slices)
    R := Matrix(Rationals(), 1, Rank(X), Eltseq(r));
    off := FractionalPart((R * ChangeRing(GramMatrix(X), Rationals()) * Transpose(R))[1, 1]);
    counts := [0 : i in [0..N]];
    lo := 0;
    for j in [1..slices] do
        hi := (j eq slices) select N else Floor(N * (j / slices)^(2 / Rank(X)));
        if hi le lo and j lt slices then continue; end if;
        // [lo, hi] closed, so skip the shared endpoint after the first slice
        M := Multiset([c[2] : c in CloseVectors(X, -r, lo, hi)]);
        for nm in MultisetToSet(M) do
            if j gt 1 and nm eq lo then continue; end if;
            counts[Integers() ! (nm - off) + 1] +:= Multiplicity(M, nm);
        end for;
        lo := hi;
    end for;
    return off, counts;
end function;

intrinsic ThetaSeriesGlued(L::Lat, N::RngIntElt : MaxVectorsPerCall := 10^6, BlockRank := 3) -> RngSerPowElt
{The theta series, the sum of q^(x.x) over x in L, of the positive definite integral
lattice L to absolute precision N + 1, the same series as ThetaSeries(L, N).
It is computed by gluing the coset theta series of mutually orthogonal
sublattices of rank at most BlockRank, so it enumerates about N^(BlockRank/2)
vectors per coset instead of the N^(n/2) that ThetaSeries enumerates.  The
default BlockRank 3 was fastest on ranks 6-12 at N = 149 (rank 12: about 0.1 s
per lattice; 2 makes the glue group and the denominators too large).
MaxVectorsPerCall bounds the vectors held in memory at once.}
    require IsPositiveDefinite(GramMatrix(L)) : "L must be positive definite";
    require BlockRank ge 1 : "BlockRank must be positive";
    Z := Integers(); Q := Rationals();
    G0 := GramMatrix(L);
    require forall{x : x in Eltseq(G0) | IsIntegral(x)} : "L must be integral";
    n := Rank(L);
    PS<q> := PowerSeriesRing(Z);
    if n le 1 or N le 0 then
        return PS ! Eltseq(ThetaSeries(L, N)) + O(q^(N + 1));
    end if;
    G := ChangeRing(GramMatrix(LLL(L)), Z);
    // Balanced block ranks r_1, ..., r_m <= BlockRank (at least two blocks).
    // Block t is the orthogonal complement of e_1..e_{s_(t-1)} inside the span
    // of e_1..e_{s_t}, s_t = r_1 + ... + r_t, so the blocks are mutually
    // orthogonal and their sum has finite index in L.
    m := Max(2, Ceiling(n / BlockRank));
    sizes := [n div m + (i le n mod m select 1 else 0) : i in [1..m]];
    cum := [&+sizes[1..t] : t in [1..m]];
    blocks := [* *];
    for t in [1..m] do
        st := cum[t]; sp := t eq 1 select 0 else cum[t - 1];
        if sp eq 0 then
            K := IdentityMatrix(Z, st);
        else
            K := BasisMatrix(Kernel(Submatrix(G, 1, 1, st, sp)));   // x in Z^st with x G e_j = 0, j <= sp
        end if;
        Append(~blocks, HorizontalJoin(K, ZeroMatrix(Z, Nrows(K), n - st)));
    end for;
    assert [Nrows(B) : B in blocks] eq sizes;
    // per block: Gram, projection coordinates of L's basis, P_X basis and class map
    function projection_data(pr)
        d := LCM([Denominator(x) : x in Eltseq(pr)]);
        H := HermiteForm(ChangeRing(d * pr, Z));
        bas := (1 / d) * ChangeRing(Matrix([r : r in Rows(H) | not IsZero(r)]), Q);
        inv := bas^-1;                                   // X-coordinates -> P_X coordinates
        F := FreeAbelianGroup(Nrows(bas));
        Qt, pi := quo<F | [F ! Eltseq(ChangeRing(r, Z)) : r in Rows(inv)]>;
        cls := func<v | pi(F ! Eltseq(ChangeRing(v * inv, Z)))>;
        return bas, Qt, pi, cls;
    end function;
    GX := [* *]; PR := [* *]; BAS := [* *]; QT := []; PI := [* *]; CLS := [* *];
    for B in blocks do
        Gb := ChangeRing(B * G * Transpose(B), Q);
        pr := ChangeRing(G * Transpose(B), Q) * Gb^-1;
        bas, Qt, pi, cls := projection_data(pr);
        Append(~GX, Gb); Append(~PR, pr); Append(~BAS, bas);
        Append(~QT, Qt); Append(~PI, pi); Append(~CLS, cls);
    end for;
    // H = image of L in the sum of the P_X/X, generated by the images of L's basis
    D, inj, proj := DirectSum(QT);
    H := sub<D | [&+[inj[t](CLS[t](PR[t][i])) : t in [1..m]] : i in [1..n]]>;
    // slices per coset call, from the volume estimate of the vector count
    function nslices(Gb)
        r := Nrows(Gb);
        vol := Pi(RealField(10))^(r / 2) / Gamma(RealField(10) ! (r / 2 + 1));
        est := vol * N^(r / 2) / Sqrt(RealField(10) ! Determinant(Gb));
        return Max(1, Ceiling(est / MaxVectorsPerCall));
    end function;
    // Products are taken in q with integral exponents: the fractional offsets of
    // a glued tuple sum to an integer (x in L has integral norm), which shifts
    // the product.  So the degree is N, whatever the denominators of the P_t.
    S<t> := PowerSeriesRing(Z, N + 1);
    XL := [* LatticeWithGram(ChangeRing(GX[b], Z)) : b in [1..m] *];
    SL := [nslices(GX[b]) : b in [1..m]];
    TH := [AssociativeArray() : b in [1..m]];
    OFF := [AssociativeArray() : b in [1..m]];
    tot := S ! 0;
    for h in H do
        prod := S ! 1; shift := 0;
        for b in [1..m] do
            c := proj[b](D ! h);
            if not IsDefined(TH[b], c) then
                r := RSpace(Q, sizes[b]) ! (Vector(Q, Eltseq(c @@ PI[b])) * BAS[b]);
                off, counts := coset_theta(XL[b], r, N, SL[b]);
                TH[b][c] := (S ! counts) + O(t^(N + 1));
                OFF[b][c] := off;
            end if;
            prod *:= TH[b][c];
            shift +:= OFF[b][c];
        end for;
        shift := Z ! shift;                    // integral: the offsets of L's vectors
        if shift le N then tot +:= t^shift * prod; end if;
    end for;
    vprintf ThetaGlue, 1 : "rank %o = %o, %o glue classes, coset thetas %o\n",
        n, sizes, #H, [#Keys(T) : T in TH];
    return PS ! [Coefficient(tot, k) : k in [0..N]] + O(q^(N + 1));
end intrinsic;

intrinsic ThetaSeriesFast(L::Lat, N::RngIntElt) -> RngSerPowElt
{The theta series of the positive definite lattice L to absolute precision N + 1,
the same series as ThetaSeries(L, N): by ThetaSeriesGlued from rank 6 on, where it
wins (rank 7 at N = 149: ThetaSeries 0.3 s, ThetaSeriesGlued 0.01 s per lattice;
ThetaSeries cannot reach N = 149 at rank 10-12 at all), and by ThetaSeries below that or for a lattice that is not
integral.}
    if Rank(L) ge 6 and forall{x : x in Eltseq(GramMatrix(L)) | IsIntegral(x)} then
        return ThetaSeriesGlued(L, N);
    end if;
    return ThetaSeries(L, N);
end intrinsic;
