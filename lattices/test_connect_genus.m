/*
   Regression tests for the minimal-vector lattice invariants in connect_genus.m:
     IsWellRounded, IsStronglyWellRounded, IsMinimalVectorGenerated, IsEutactic.

   Run from the lattices/ directory with:
       magma test_connect_genus.m

   NOTE: this attaches connect_genus.m (and its dependencies hash.m,
   canonical_form.m).  Because Magma resolves every reference in a package the
   first time one of its intrinsics is called, all references in connect_genus.m
   must be defined for these tests to run; in particular AutOrbits must not refer
   to an undefined identifier.
*/

Attach("hash.m");
Attach("canonical_form.m");
Attach("connect_genus.m");

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

printf "\n%o failure(s)\n", nfail;
assert nfail eq 0;
print "ALL TESTS PASSED";
