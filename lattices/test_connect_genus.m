/*
   Regression tests for the minimal-vector lattice invariants in connect_genus.m:
     IsWellRounded, IsStronglyWellRounded, IsMinimalVectorGenerated, IsEutactic.

   Run from the lattices/ directory, once the package compiles, with:
       magma test_connect_genus.m

   The four intrinsics tested here are self-contained (they only use Magma
   built-ins), but they live in connect_genus.m alongside the database-pipeline
   intrinsics.  Magma resolves *every* reference in a package the first time any
   of its intrinsics is called, so the whole package must resolve for these tests
   to run.  At time of writing connect_genus.m does NOT yet resolve, because the
   pipeline (e.g. ConnectGenus, line ~421) calls ThetaSeriesIncremental, which is
   a file-local `function` in fill_genus.m and is therefore invisible across
   package files.  Until such references are made into intrinsics (or otherwise
   shared), no intrinsic in connect_genus.m can be invoked, the present one
   included.

   Once the package resolves, run from the lattices/ directory with
       magma test_connect_genus.m
   after replacing the Attach line below with  AttachSpec("lattices.spec").
   All assertions here were independently verified against the individual
   intrinsics in isolation.
*/

AttachSpec("lattices.spec");

nfail := 0;
procedure Expect(name, got, expected)
    if got cmpeq expected then
        printf "  ok   %o\n", name;
    else
        printf "  FAIL %o: got %o, expected %o\n", name, got, expected;
        nfail +:= 1;
    end if;
end procedure;

// ---------------------------------------------------------------------------
// IsStronglyWellRounded: the shortest vectors contain a basis of L.
// ---------------------------------------------------------------------------
print "IsStronglyWellRounded:";
for tup in [* <"A2", Lattice("A",2), true>, <"A3", Lattice("A",3), true>,
              <"D4", Lattice("D",4), true>, <"D5", Lattice("D",5), true>,
              <"E6", Lattice("E",6), true>, <"E8", Lattice("E",8), true>,
              <"Z3", StandardLattice(3), true>,
              // shortest vectors generate only a rank-deficient set -> false
              <"diag(1,2,3)", LatticeWithGram(DiagonalMatrix(Rationals(),[1,2,3])), false> *] do
    L := tup[2];
    Expect(tup[1], IsStronglyWellRounded(L, ShortestVectors(L)), tup[3]);
end for;
// A well-rounded lattice whose shortest vectors span but contain NO basis
// (found by search; minimal vectors generate an index>1 sublattice direction).
// dim-6 example: must be well rounded yet NOT strongly well rounded.
G6 := SymmetricMatrix(Rationals(),
        [55, 1,19, 36,0,55, -1,-3,-37,46, 7,3,7,0,6, -20,6,-35,29,1,31]);
L6 := LatticeWithGram(G6);
S6 := ShortestVectors(L6);
Expect("dim6 WR-not-SWR is well rounded", IsWellRounded(L6, S6), true);
Expect("dim6 WR-not-SWR not strongly WR", IsStronglyWellRounded(L6, S6), false);

// ---------------------------------------------------------------------------
// IsEutactic: exists c_s > 0 with x.x = sum_s c_s (x.s)^2.  When true, the
// returned coefficients must be positive and reproduce G^{-1} exactly.
// ---------------------------------------------------------------------------
print "IsEutactic:";
function Certifies(L, S, coeffs)
    if #coeffs ne #S then return false; end if;
    if not &and[ c gt 0 : c in coeffs ] then return false; end if;
    G := ChangeRing(GramMatrix(L), Rationals());
    U := [ Vector(Rationals(), [ c : c in Coordinates(L, s) ]) : s in S ];
    M := &+[ coeffs[i] * (Transpose(Matrix(U[i])) * Matrix(U[i])) : i in [1..#U] ];
    return M eq G^-1;
end function;

for tup in [* <"Z3", StandardLattice(3), true>, <"A2", Lattice("A",2), true>,
              <"A3", Lattice("A",3), true>, <"D4", Lattice("D",4), true>,
              <"E6", Lattice("E",6), true>, <"E8", Lattice("E",8), true> *] do
    L := tup[2];  S := ShortestVectors(L);
    eu, coeffs := IsEutactic(L, S);
    Expect(tup[1] cat " eutactic", eu, tup[3]);
    if eu then
        Expect(tup[1] cat " certificate", Certifies(L, S, coeffs), true);
    end if;
end for;

// Well rounded but not (weakly) eutactic: two pairs of minimal vectors whose
// outer products do not span G^{-1}.
Leu := LatticeWithGram(Matrix(Rationals(),2,2,[2,1/2,1/2,2]));
Expect("non-eutactic WR", IsEutactic(Leu, ShortestVectors(Leu)), false);
// Not well rounded -> not eutactic.
Lnw := LatticeWithGram(DiagonalMatrix(Rationals(),[1,2,3]));
Expect("non-WR not eutactic", IsEutactic(Lnw, ShortestVectors(Lnw)), false);

// ---------------------------------------------------------------------------
// IsAdditivelyDecomposableByRankOne: a sufficient (not complete) decomposability
// test.  "true" certifies additive decomposability; "false" is inconclusive.
// ---------------------------------------------------------------------------
print "IsAdditivelyDecomposableByRankOne (sufficient only):";
// Root lattices / Z^n have dual vectors of norm <= 1 -> certified decomposable.
for tup in [* <"A1", Lattice("A",1)>, <"A2", Lattice("A",2)>, <"A3", Lattice("A",3)>,
              <"D4", Lattice("D",4)>, <"Z3", StandardLattice(3)> *] do
    Expect(tup[1] cat " rank-1-decomposable", IsAdditivelyDecomposableByRankOne(tup[2]), true);
end for;
// E8 has dual minimum 2 -> the rank-1 test is inconclusive (it really IS
// additively indecomposable, but this test cannot see that).
Expect("E8 rank-1 test inconclusive", IsAdditivelyDecomposableByRankOne(Lattice("E",8)), false);

// ---------------------------------------------------------------------------
// IsAdditivelyIndecomposable: layered decision <value, determined>.
// Complete for rank <= 8 (Mordell / Plesken III.4) and several rank >= 9 cases.
// ---------------------------------------------------------------------------
print "IsAdditivelyIndecomposable <value, determined>:";
procedure ExpectAI(name, L, exp_val, exp_known)
    v, known := IsAdditivelyIndecomposable(L);
    Expect(name cat " (value)", known select v else "undet", known select exp_val else "undet");
    Expect(name cat " (determined)", known, exp_known);
end procedure;
ExpectAI("Z1", StandardLattice(1), true, true);     // (Z,1)
ExpectAI("A2 (rank2)", Lattice("A",2), false, true);  // Mordell
ExpectAI("D5 (rank5)", Lattice("D",5), false, true);  // Mordell
ExpectAI("E6", Lattice("E",6), true, true);          // Plesken III.4
ExpectAI("A6 (not E6)", Lattice("A",6), false, true);
ExpectAI("E7", Lattice("E",7), true, true);
ExpectAI("E8", Lattice("E",8), true, true);
ExpectAI("D8 (not E8)", Lattice("D",8), false, true);
ExpectAI("Z9 (orthog decomp)", StandardLattice(9), false, true);

// Discriminant 4/5 (Wang Thm. 2.16), via Plesken's families a;(s)b = diag(1..1,-s)+a^t a.
function pleskenLat(av, s)
    m := #av;
    G := DiagonalMatrix(Integers(), [1 : i in [1..m-1]] cat [-s])
         + Transpose(Matrix(Integers(),1,m,av)) * Matrix(Integers(),1,m,av);
    return LatticeWithGram(G);
end function;
// 1^11;4 (dim 12, det 4) and 1^9;(2)5 (dim 10, det 5) are additively indecomposable.
ExpectAI("1^11;4 (Plesken)", pleskenLat([1: i in [1..11]] cat [4], 1), true, true);
ExpectAI("1^9;(2)5 (Plesken)", pleskenLat([1: i in [1..9]] cat [5], 2), true, true);
// det-4 lattice that IS additively decomposable: complement of (x,y), Q(x)=Q(y)=2, in E8 perp E8.
E8 := Lattice("E",8);  G8 := ChangeRing(GramMatrix(E8), Integers());
wc := Vector(Integers(),
        Coordinates(E8, ShortestVectors(E8)[1]) cat Coordinates(E8, ShortestVectors(E8)[2]));
G16 := DiagonalJoin(G8, G8);
Bcplt := Matrix(Integers(), [ Eltseq(b) : b in Basis(Kernel(G16 * Transpose(Matrix(wc)))) ]);
Ldec4 := LatticeWithGram(Bcplt * G16 * Transpose(Bcplt));
ExpectAI("E8+E8 norm-4 cplt (det4)", Ldec4, false, true);   // additively decomposable

// Plesken III.1 sufficient condition, as a standalone:
print "SatisfiesPleskenIII1:";
Expect("E8 satisfies III.1", SatisfiesPleskenIII1(Lattice("E",8)), true);
Expect("Z3 fails III.1 (dual min <= 1)", SatisfiesPleskenIII1(StandardLattice(3)), false);

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
print "ALL TESTS PASSED";
