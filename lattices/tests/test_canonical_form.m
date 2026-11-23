// CanonicalForm chooses its characteristic vector set among V_ms and V_cvp of the
// lattice and of its dual.  V_best_with_dual_fast must make the same choice as
// V_best_with_dual, so the canonical forms below, computed with the code before
// it, must not change.  Between them these lattices choose each of the four sets.
// Also checks SuccessiveMinimaFaster against SuccessiveMinima.
AttachSpec("lattices.spec");
load "tests/assertions.m";

procedure()
results := NewResults();
Z := Integers();
SetSeed(1);

// <name, gram, canonical form before V_best_with_dual_fast>
cases := [* <"I5+<3>", DiagonalMatrix(Z, [1,1,1,1,1,3]), DiagonalMatrix(Z, [1,1,1,1,1,3])>,
  <"I6+<7>", DiagonalMatrix(Z, [1,1,1,1,1,1,7]), DiagonalMatrix(Z, [1,1,1,1,1,1,7])>,
  <"D4+<3>", DiagonalJoin(CartanMatrix("D4"), DiagonalMatrix(Z, [3])),
    Matrix(Z, 5, 5, [2,0,0,-1,0, 0,2,0,-1,0, 0,0,2,-1,0, -1,-1,-1,2,0, 0,0,0,0,3])>,
  <"E6", CartanMatrix("E6"),
    Matrix(Z, 6, 6, [2,1,0,1,1,2, 1,2,0,1,1,2, 0,0,2,0,0,1, 1,1,0,2,1,2, 1,1,0,1,2,2, 2,2,1,2,2,4])>,
  <"3.24.48.2", Matrix(Z, 3, 3, [3,1,-1, 1,4,1, -1,1,3]), Matrix(Z, 3, 3, [3,-1,1, -1,4,2, 1,2,4])>,
  <"A3+<2,6>", DiagonalJoin(CartanMatrix("A3"), DiagonalMatrix(Z, [2,6])),
    Matrix(Z, 5, 5, [2,1,-1,0,0, 1,2,-1,0,0, -1,-1,2,0,0, 0,0,0,2,0, 0,0,0,0,6])>,
  <"D5", CartanMatrix("D5"),
    Matrix(Z, 5, 5, [2,1,1,1,1, 1,2,1,1,1, 1,1,2,1,1, 1,1,1,2,0, 1,1,1,0,2])>,
  <"<2,2,3,3,6>", DiagonalMatrix(Z, [2,2,3,3,6]), DiagonalMatrix(Z, [2,2,3,3,6])> *];

for c in cases do
    name, G, expected := Explode(c);
    C, U := CanonicalForm(G);
    AssertEqual(~results, C, ChangeRing(expected, Rationals()), name cat ": canonical form unchanged");
    AssertTrue(~results, C eq U * ChangeRing(G, Rationals()) * Transpose(U), name cat ": C = U G U^t");
    T := RandomGLnZ(Nrows(G), 33, 17);
    AssertEqual(~results, CanonicalForm(T * G * Transpose(T)), C, name cat ": invariant under a change of basis");
end for;

// SuccessiveMinimaFaster, on orthogonal sums and on indecomposable lattices
for G in [* DiagonalMatrix(Z, [1,1,1,1,1,1,1,1,13]),
          DiagonalJoin(CartanMatrix("E7"), DiagonalMatrix(Z, [1,1,3])),
          DiagonalJoin(CartanMatrix("A2"), Matrix(Z, 3, 3, [3,1,-1, 1,4,1, -1,1,3])),
          CartanMatrix("E8"),
          Matrix(Z, 3, 3, [3,1,-1, 1,4,1, -1,1,3]) *] do
    T := RandomGLnZ(Nrows(G), 33, 17);
    L := LatticeWithGram(T * G * Transpose(T));
    AssertEqual(~results, SuccessiveMinimaFaster(L), SuccessiveMinima(L),
                Sprintf("SuccessiveMinimaFaster, rank %o det %o", Nrows(G), Determinant(G)));
end for;

Report(~results, "test_canonical_form");
end procedure();
