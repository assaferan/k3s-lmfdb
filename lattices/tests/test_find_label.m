// FindLabel against a tiny on-disk database built in a temporary directory, so
// the suite needs no pipeline output.  Indefinite lattices are stored with hash
// "\N"; FindLabel used to drop those rows and return "\N" for every indefinite
// lattice, which nulled dual_label, even_sublattice and primitive_scaling for
// all of them.
AttachSpec("lattices.spec");
load "tests/assertions.m";

procedure()
results := NewResults();

hash_fmt := Read("lat_hash.format");
here := GetCurrentDirectory();
tmp := Split(Pipe("mktemp -d", ""), "\n")[1];
ChangeDirectory(tmp);
Write("lat_hash.format", hash_fmt : Overwrite := true);

// write one genus: its hash-function record and its lattice rows
write_genus := procedure(L, rows)
    n := Rank(L);
    s := Signature(GramMatrix(L));
    gh := IntegerToString(HashGenus(L));
    Write(LabelPath("genera_hash", n, s, gh : Create := true), "\\N" : Overwrite := true);
    Write(LabelPath("lattice_hashes", n, s, gh : Create := true), Join(rows, "\n") : Overwrite := true);
end procedure;

// the hyperbolic plane U, alone in its genus
U := LatticeWithGram(Matrix(Integers(), 2, 2, [0, 1, 1, 0]) : CheckPositive := false);
write_genus(U, ["2.1.1.0.1|\\N|\\N|{0,1,1,0}"]);
AssertEqual(~results, FindLabel(U), "2.1.1.0.1", "FindLabel U, one indefinite class");
// any basis of U finds it
U2 := LatticeWithGram(Matrix(Integers(), 2, 2, [0, 1, 1, 2]) : CheckPositive := false);
AssertEqual(~results, FindLabel(U2), "2.1.1.0.1", "FindLabel U in another basis");

// two stored classes in an indefinite genus cannot be told apart: stay null
write_genus(U, ["2.1.1.0.1|\\N|\\N|{0,1,1,0}", "2.1.1.0.2|\\N|\\N|{0,1,1,0}"]);
AssertEqual(~results, FindLabel(U), "\\N", "FindLabel indefinite genus with two classes");

// definite control: a single stored class is still found through the hash path
I2 := StandardLattice(2);
write_genus(I2, ["2.2.1.5.1|1|1|{1,0,0,1}"]);
AssertEqual(~results, FindLabel(I2), "2.2.1.5.1", "FindLabel I2, definite");

ChangeDirectory(here);
System("rm -rf '" * tmp * "'");
Report(~results, "test_find_label");
end procedure();
