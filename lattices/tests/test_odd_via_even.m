// GenusRepresentativesFaster finds the genus of an odd lattice of even
// determinant through its even sublattice (odd_via_even.m).  It must give one
// lattice per class: the right class number, the full mass, no two isometric.
AttachSpec("lattices.spec");
load "tests/assertions.m";

procedure()
results := NewResults();
Z := Integers();

pairwise_distinct := function(R)
    for i in [1 .. #R] do
        for j in [i + 1 .. #R] do
            if IsIsometric(R[i], R[j]) then return false; end if;
        end for;
    end for;
    return true;
end function;

check := procedure(~results, G, name)
    L := LatticeWithGram(G);
    R := [x : x in GenusRepresentativesFaster(L : odd_via_even_rank := 3)];
    W := GenusRepresentativesFaster(L : odd_via_even_rank := Rank(L) + 1);   // the p = 3 walk
    AssertEqual(~results, #R, #W, name cat ": class number agrees with the p = 3 walk");
    AssertTrue(~results, &+[Rationals() | 1 / #AutomorphismGroupFaster(x) : x in R] eq Mass(L),
               name cat ": mass");
    AssertTrue(~results, forall{x : x in R | Genus(x) eq Genus(L)}, name cat ": all in the genus");
    AssertTrue(~results, pairwise_distinct(R), name cat ": pairwise non-isometric");
end procedure;

check(~results, DiagonalMatrix(Z, [1, 1, 2]), "I2 + <2>");
check(~results, DiagonalMatrix(Z, [1, 2, 3, 4]), "<1,2,3,4>");
check(~results, DiagonalJoin(CartanMatrix("A2"), DiagonalMatrix(Z, [1, 1, 2])), "A2 + I2 + <2>");
check(~results, DiagonalJoin(CartanMatrix("D4"), DiagonalMatrix(Z, [1, 6])), "D4 + <1,6>");
check(~results, DiagonalMatrix(Z, [1, 1, 1, 1, 1, 1, 1, 1, 4]), "I8 + <4>");
check(~results, DiagonalMatrix(Z, [1, 1, 1, 1, 2, 2, 2, 2]), "I4 + 2I4");
check(~results, DiagonalJoin(CartanMatrix("E7"), DiagonalMatrix(Z, [1, 1, 2])), "E7 + I2 + <2>");

// LMFDB genus 3.24.48.2: class number 2
L := LatticeWithGram(Matrix(Z, 3, 3, [3,1,-1, 1,4,1, -1,1,3]));
AssertEqual(~results, #GenusRepresentativesFaster(L : odd_via_even_rank := 3), 2, "3.24.48.2 class number");

// GenusRepresentativesOddViaEven given the even classes directly
L := LatticeWithGram(DiagonalMatrix(Z, [1, 1, 1, 1, 2, 2]));
L0 := LatticeWithGram(GramMatrix(EvenSublattice(L)));
R, ok := GenusRepresentativesOddViaEven(L : even_reps := [x : x in GenusRepresentativesFaster(L0)]);
AssertTrue(~results, ok, "I4 + 2I2 from given even classes: mass");
AssertEqual(~results, #R, #GenusRepresentativesFaster(L : odd_via_even_rank := 100),
            "I4 + 2I2 from given even classes: class number");

Report(~results, "test_odd_via_even");
end procedure();
