import "canonical_form.m" : test_canonical, num_V;
import "tests/_L12a+.m" : L12a;
// This is still impossible because some of these lattices have
// characteristic vector sets that are too large.
// time cans := [CanonicalForm(A) : A in L12a];
nums := [num_V(ChangeRing(A,Rationals())) : A in L12a]; // time: 103.530
assert nums eq [ 484, 304, 356, 122, 276, 2556, 33252, 742, 894, 278, 308, 1868, 4544, 8256, 222, 220, 618, 1186, 13410, 742, 484, 332, 206, 58, 676, 248, 164, 197, 886, 118, 454, 164, 240, 246, 216, 2556, 502, 820, 499, 272, 58, 240, 348, 204, 258, 232, 142, 110, 56, 276, 106, 438, 656 ];

good_idxs := [j : j in [1..#nums] | nums[j] le 8000];
// last 3 lattices that we need to take care of
bad_idxs := [j : j in [1..#nums] | nums[j] gt 8000];
assert #bad_idxs eq 3;
time cans := [CanonicalForm(L12a[j]) : j in good_idxs];

// We can actually also do L12a[14], which has 8256 vectors in the vector set,
// but this takes 3058.530 seconds
