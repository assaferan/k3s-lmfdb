/*
  tDesign(L, H) returns the maximal t such that the chosen shell of L,
  rescaled to S^{n-1}, is a spherical t-design.
  H consists of representatives of this chosen shell up to +/-

  Criterion: X is a t-design  <=>  sum_{x,y in X} C_k^lambda(<x,y>) = 0
  for all 1 <= k <= t, where lambda = (n-2)/2 and vectors are unit-normalized.
  Each sum is automatically >= 0, so the strength is the largest t before the
  first nonzero sum. (n = 2 uses Chebyshev T_k.) All arithmetic is exact.
*/

function kernel_polys(n, tmax)
    R<x> := PolynomialRing(Rationals());
    polys := [R | ];
    if n eq 2 then                         // Chebyshev T_k
        if tmax ge 1 then Append(~polys, x); end if;
        Tprev2 := R!1; Tprev1 := x;
        for k in [2..tmax] do
            Tk := 2*x*Tprev1 - Tprev2;
            Append(~polys, Tk);
            Tprev2 := Tprev1; Tprev1 := Tk;
        end for;
    else                                   // Gegenbauer C_k^lambda
        lambda := (n-2)/2;
        C0 := R!1; C1 := 2*lambda*x;
        if tmax ge 1 then Append(~polys, C1); end if;
        Cprev2 := C0; Cprev1 := C1;
        for k in [2..tmax] do
            Ck := (2*(k+lambda-1)*x*Cprev1 - (k+2*lambda-2)*Cprev2)/k;
            Append(~polys, Ck);
            Cprev2 := Cprev1; Cprev1 := Ck;
        end for;
    end if;
    return polys;                          // polys[k] has degree k
end function;

// only needs half the short vectors
// This one is O((#Hh)^2)
function shell_design_strength(L, Hh : MaxDegree := 20)
    n := Rank(L);
    
    error if #Hh eq 0, "no vectors of that norm";

    m := Norm(Hh[1]);
    printf "n = %o, m = %o, |X| = %o (half-set %o)\n", n, m, 2*#Hh, #Hh;

    Hist := AssociativeArray();                       // <h,h'>/m over the half-set
    for x in Hh do for y in Hh do
        u := InnerProduct(x,y)/m;
        if IsDefined(Hist,u) then Hist[u] +:= 1; else Hist[u] := 1; end if;
    end for; end for;

    polys := kernel_polys(n, MaxDegree);
    s := 0; failed := 0; k := 2;                      // odd k vanish identically
    while k le MaxDegree do
        Sk := &+[ Rationals() | Hist[u]*Evaluate(polys[k], u) : u in Keys(Hist) ];
        if Sk eq 0 then s := k; else failed := k; break; end if;
        k +:= 2;
    end while;
    tdes := s+1;
    if failed ne 0 then
        printf "Spherical %o-design; first nonzero even sum at degree %o.\n", tdes, failed;
    else
        printf "Spherical %o-design (even sums vanish through degree %o).\n", tdes, s;
    end if;
    return tdes;
end function;

// When #Hh is large, we can have a linear algorithm
// in small dimension by running over a basis for the
// space of harmonic polynomials

function GHarmonics(Ginv, n, k)
    R := PolynomialRing(Rationals(), n);
    mons := MonomialsOfDegree(R, k);
    if k le 1 then return mons; end if;              // linear forms are harmonic
    lower := MonomialsOfDegree(R, k-2);
    Lap := ZeroMatrix(Rationals(), #mons, #lower);
    for a in [1..#mons] do
        f := mons[a]; lap := R!0;
        for i in [1..n] do for j in [1..n] do
            if Ginv[i,j] ne 0 then
                lap +:= Ginv[i,j]*Derivative(Derivative(f, i), j);
            end if;
        end for; end for;
        for b in [1..#lower] do
            Lap[a,b] := MonomialCoefficient(lap, lower[b]);
        end for;
    end for;
    K := Kernel(Lap);                                 // {v : v*Lap = 0}
    return [ &+[ R | v[a]*mons[a] : a in [1..#mons] ] : v in Basis(K) ];
end function;

// This is O(#H)
function shell_design_strength_harmonic(L, H : MaxDegree := 12)
    n := Rank(L);  G := ChangeRing(GramMatrix(L), Rationals());  Ginv := G^-1;

    coords := [ Coordinates(s) : s in H ];   // half-shell (sequence of vectors)
    error if #coords eq 0, "no vectors of that norm";

    m := Norm(H[1]);
    printf "n = %o, m = %o, |X| = %o\n", n, m, 2*#coords;

    s := 0; failed := 0; k := 2;
    while k le MaxDegree do
        ok := true;
        for P in GHarmonics(Ginv, n, k) do
            if &+[ Rationals() | Evaluate(P, c) : c in coords ] ne 0 then
                ok := false; break;                   // full sum = 2*half sum (even deg)
            end if;
        end for;
        if ok then s := k; else failed := k; break; end if;
        k +:= 2;
    end while;
    tdes := s+1;
    if failed ne 0 then printf "Spherical %o-design; fails at degree %o.\n", tdes, failed;
    else printf "Spherical %o-design (harmonics vanish through degree %o).\n", tdes, s; end if;
    return tdes;
end function;

// Finally, this one does not need to enumerate short vectors,
// at the cost of computing spaces of modular forms

// We probably will not need these two functions, as 
// we only care about the case where H is the shortest vectors
// and then this does not help

function lattice_level(G)                 // level of an even lattice: ell*G^-1 even integral
    Gi := G^-1; n := Nrows(G); L := 1;
    for i in [1..n] do
        L := LCM(L, Denominator(Gi[i,i]/2));
        for j in [i+1..n] do L := LCM(L, Denominator(Gi[i,j])); end for;
    end for;
    return L;
end function;

function theta_harmonic_vanishes(L, P : Verbose := true)
    n := Rank(L);  G := GramMatrix(L);
    k := TotalDegree(P);
    w := (n + 2*k);  error if IsOdd(w), "odd rank -> half-integral weight; handle separately";
    w := w div 2;
    ell := lattice_level(G);
    D := (-1)^(n div 2) * (Integers()!Determinant(G));
    chi := KroneckerCharacter(D, FullDirichletGroup(ell));
    M := ModularForms(chi, w);
    B := PrecisionBound(M);                            // Sturm bound
    coeff := [ Rationals() | 0 : i in [1..B] ];
    for s in ShortVectors(L, 2*(B-1)) do               // small shells only
        idx := (s[2] div 2) + 1;
        coeff[idx] +:= 2*Evaluate(P, Coordinates(s[1]));
    end for;
    vanishes := forall{ a : a in coeff | a eq 0 };
    if Verbose then
        printf "wt %o, level %o, Sturm %o: theta_{L,P} %o\n", w, ell, B,
            vanishes select "= 0 (all shells design for this P)" else "=/= 0";
    end if;
    return vanishes;
end function;

function harmonic_Molien_dims(G, prec)
    Ms := MolienSeries(ChangeRing(G, Rationals()));   // group must be over a field for MolienSeries
                                                       // (Aut(L) comes as a GrpMat over Z)
    PS<t> := PowerSeriesRing(Rationals(), prec+2);
    h := (1 - t^2) * (PS!Ms);                      // strip the r^2 factor -> harmonic invariants
    return [ Integers()!Coefficient(h, k) : k in [0..prec] ];   // dims[k+1] = dim H_k^G
end function;

// Aut-invariant degree-k G-harmonics. Uses the RIGHT action P(c*g)=P(c),
// matching how Magma's automorphisms move lattice coordinates (c -> c*g).
function GHarmonics_invariant(G, Ginv, n, k)
    H := GHarmonics(Ginv, n, k);  d := #H;
    if d eq 0 then return H; end if;
    R := Parent(H[1]);   // reuse the harmonics' own ring; a fresh PolynomialRing(Q,n)
                         // is a distinct object and cross-ring MonomialCoefficient hangs
    mons := MonomialsOfDegree(R, k);
    Hmat := Matrix([ [ MonomialCoefficient(P, mn) : mn in mons ] : P in H ]);
    fixed := VectorSpace(Rationals(), d);
    for s in Generators(G) do
        subst := [ &+[ R | s[i,j]*R.i : i in [1..n] ] : j in [1..n] ];   // y_j -> (y*s)_j
        Img := Matrix([ [ MonomialCoefficient(Evaluate(P, subst), mn) : mn in mons ] : P in H ]);
        Ms  := Solution(Hmat, Img);                                      // Ms*Hmat = Img
        fixed := fixed meet Kernel(Ms - IdentityMatrix(Rationals(), d));
    end for;
    return [ &+[ R | a[i]*H[i] : i in [1..d] ] : a in Basis(fixed) ];
end function;

// Here, G is the automorphism group of L
function universal_design_strength(L, G : MaxDegree := 30)
    dims := harmonic_Molien_dims(G, MaxDegree);
    k0 := 0;
    for k in [1..MaxDegree] do
        if dims[k+1] gt 0 then k0 := k; break; end if;
    end for;
    if k0 eq 0 then
        printf "No invariant harmonics through degree %o; every shell is (>=%o)-design.\n",
               MaxDegree, MaxDegree;
        return MaxDegree;
    end if;
    printf "First Aut(L)-invariant harmonic at degree %o (dim %o).\n", k0, dims[k0+1];
    printf "=> every shell of L is a %o-design (exact unless that invariant's\n", k0-1;
    printf "   theta series vanishes identically -- the extremal case).\n";
    return k0-1;
end function;

//  Molien dims say *where* invariant harmonics live; only there do we build the
//  (few) invariants and touch the shell. Degrees with no invariants are designs
//  for free. Needs Aut(L); pass a precomputed group via Aut:= to avoid recomputing.
function shell_design_strength_Molien(L, H, A : MaxDegree := 16,
                                                MaxHarmonicDim := 50000)
    n := Rank(L);  G := ChangeRing(GramMatrix(L), Rationals());  Ginv := G^-1;

    coords := [ Coordinates(s) : s in H ];      // half-shell (sequence of vectors)
    error if #coords eq 0, "no vectors of that norm";
    m := Norm(H[1]);

    dims := harmonic_Molien_dims(A, MaxDegree);
    printf "n = %o, m = %o, |X| = %o, |Aut(L)| = %o\n", n, m, 2*#coords, #A;

    s := 0; failed := 0; capped := 0;  k := 2;                          // odd k auto-vanish
    while k le MaxDegree do
        if dims[k+1] eq 0 then
            s := k;                                                     // no invariants: design, free
        elif Binomial(n+k-1, k) gt MaxHarmonicDim then
            capped := k; break;                                         // harmonic space too big to build
        else
            inv := GHarmonics_invariant(A, Ginv, n, k);
            assert #inv eq dims[k+1];                                   // construction sanity vs Molien
            ok := true;
            for P in inv do
                if &+[ Rationals() | Evaluate(P, c) : c in coords ] ne 0 then ok := false; break; end if;
            end for;
            if ok then s := k; else failed := k; break; end if;
        end if;
        k +:= 2;
    end while;

    tdes := s+1;
    if failed ne 0 then
        printf "Shell is a spherical %o-design; fails at degree %o (a degree-%o invariant has nonzero sum).\n",
               tdes, failed, failed;
    elif capped ne 0 then
        printf "Shell is a spherical %o-design so far; degree %o has %o invariant harmonic(s) but\n",
               tdes, capped, dims[capped+1];
        printf "  dim H_%o exceeds MaxHarmonicDim -- raise the cap, or run the theta test on those.\n", capped;
    else
        printf "Shell is a spherical %o-design (checked through degree %o).\n", tdes, s;
    end if;
    return tdes;
end function;

intrinsic tDesign(L::Lat, S::SeqEnum : A := 0) -> RngIntElt
{Given a sequence S of representatives of the vectors of a certain norm m in the lattice up to +/-, 
find the largest integer t such that S is a spherical t-design 
(sum over s in S of (x.s)^t = C * x.x^(t/2) for some C, which must be (m #S)/n).}
    // The three methods agree (verified against each other on root lattices); the
    // cutoffs only choose the fastest in each regime:
    //   * direct (Gegenbauer histogram), O(#S^2)        -- small shells;
    //   * harmonic, O(#S) but builds degree-d harmonic spaces in n variables
    //     -- large shells, but only feasible in small rank;
    //   * Molien, builds only the Aut(L)-invariant harmonics -- large shells in
    //     large rank, needs the automorphism group A.
    // For shortest-vector shells the strength is small (<= 11, the Leech case), so
    // the differing internal MaxDegree caps (20/12/16) never bite.
    if #S lt 10^4 then return shell_design_strength(L,S); end if;
    if Rank(L) lt 10 then return shell_design_strength_harmonic(L,S); end if;
    require A cmpne 0 :
        "tDesign: a large shell in rank >= 10 needs the automorphism group; pass A := AutomorphismGroup(L)";
    return shell_design_strength_Molien(L,S,A);
end intrinsic;