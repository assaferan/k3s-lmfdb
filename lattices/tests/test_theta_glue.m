// ThetaSeriesGlued must return exactly ThetaSeries(L, N): same coefficients,
// same absolute precision, so Eltseq gives the same stored sequence.
AttachSpec("lattices.spec");
load "tests/assertions.m";

procedure() // forcing magma to read the full input before forking (ThetaSeriesIncremental)
results := NewResults();

Z := Integers();
same := function(L, N)
    a := ThetaSeriesGlued(L, N);
    b := ThetaSeries(L, N);
    return Eltseq(a) eq Eltseq(b) and AbsolutePrecision(a) eq AbsolutePrecision(b);
end function;

// root lattices, unimodular lattices, odd and even, ranks 2-8
for name in ["A2", "A5", "D4", "D6", "E6", "E7", "E8", "A3A1"] do
    AssertTrue(~results, same(LatticeWithGram(CartanMatrix(name)), 24), "glued theta of " cat name);
end for;
for n in [2, 3, 7] do
    AssertTrue(~results, same(StandardLattice(n), 24), Sprintf("glued theta of Z^%o", n));
end for;
// a non-diagonal odd lattice whose halves have nontrivial glue
L := LatticeWithGram(Matrix(Z, 3, 3, [2,1,0, 1,3,1, 0,1,5]));
AssertTrue(~results, same(L, 40), "glued theta of a rank-3 det-23 lattice");
// a scrambled basis must not matter
E8 := LatticeWithGram(CartanMatrix("E8"));
U := Matrix(Z, 8, 8, [1,2,0,0,0,0,0,1, 0,1,3,0,0,0,0,0, 0,0,1,1,0,0,0,0, 0,0,0,1,0,0,0,0,
                       0,0,0,0,1,2,0,0, 0,0,0,0,0,1,0,0, 0,0,0,0,0,0,1,1, 0,0,0,0,0,0,0,1]);
AssertTrue(~results, same(LatticeWithGram(U * GramMatrix(E8) * Transpose(U)), 24), "glued theta of scrambled E8");
// an odd rank-10 lattice (I + J with one diagonal entry raised) and its rescaled dual
G := Matrix(Z, 10, 10, [2,1,1,1,1,1,1,1,1,1, 1,2,1,1,1,1,1,1,1,1, 1,1,2,1,1,1,1,1,1,1,
    1,1,1,2,1,1,1,1,1,1, 1,1,1,1,2,1,1,1,1,1, 1,1,1,1,1,2,1,1,1,1, 1,1,1,1,1,1,2,1,1,1,
    1,1,1,1,1,1,1,2,1,1, 1,1,1,1,1,1,1,1,2,1, 1,1,1,1,1,1,1,1,1,3]);
L := LatticeWithGram(G);
AssertTrue(~results, same(L, 30), "glued theta of a rank-10 lattice");
AssertTrue(~results, same(Dual(L), 30), "glued theta of its rescaled dual");
// every block size must give the same series
for b in [2, 3, 4, 5, 9] do
    AssertTrue(~results, Eltseq(ThetaSeriesGlued(L, 30 : BlockRank := b)) eq Eltseq(ThetaSeries(L, 30)),
        Sprintf("glued theta of the rank-10 lattice with BlockRank %o", b));
end for;
// slicing the norm range must not change the answer
a := ThetaSeriesGlued(L, 30 : MaxVectorsPerCall := 50);
AssertTrue(~results, Eltseq(a) eq Eltseq(ThetaSeries(L, 30)), "glued theta with many slices");
// ThetaSeriesFast dispatches: glued from rank 6, ThetaSeries below or when not integral
for M in [LatticeWithGram(CartanMatrix("A4")), E8, Dual(E8 : Rescale := false), Dual(LatticeWithGram(CartanMatrix("D6")) : Rescale := false)] do
    AssertTrue(~results, Eltseq(ThetaSeriesFast(M, 20)) eq Eltseq(ThetaSeries(M, 20)),
        Sprintf("ThetaSeriesFast, rank %o, det %o", Rank(M), Determinant(M)));
end for;

// ThetaSeriesIncremental must reach its target, not stop at the last power-of-two step
// below it (it used to stop at 128 for a target of 150)
th, prec := ThetaSeriesIncremental(E8, 150, 120);
AssertEqual(~results, prec, 150, "ThetaSeriesIncremental reaches precision 150");
AssertTrue(~results, th eq Eltseq(ThetaSeries(E8, 149)), "and returns the right coefficients");

Report(~results, "test_theta_glue");
end procedure();
