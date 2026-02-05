import "canonical_form.m" : test_canonical, num_V;
import "tests/_L12a+.m" : L12a;
// This is still impossible because some of these lattices have
// characteristic vector sets that are too large.
// time cans := [CanonicalForm(A) : A in L12a];
nums := [num_V(ChangeRing(A,Rationals())) : A in L12a]; // time: 103.530
print nums;
assert nums eq [ 484, 304, 556, 508, 516, 2556, 33252, 998, 1332, 278, 1068, 1868, 5248, 8256, 
1186, 224, 1148, 5122, 13410, 998, 86546, 332, 276, 310, 676, 500, 608, 670, 
670, 368, 576, 318, 406, 890, 248, 2556, 502, 820, 492, 272, 332, 240, 348, 408,
524, 232, 146, 252, 142, 376, 222, 656, 656 ];

good_idxs := [j : j in [1..#nums] | nums[j] le 8000];
// last 3 lattices that we need to take care of
bad_idxs := [j : j in [1..#nums] | nums[j] gt 8000];
assert #bad_idxs eq 3;
time cans := [CanonicalForm(L12a[j]) : j in good_idxs];

// We can actually also do L12a[14], which has 8256 vectors in the vector set,
// but this takes 3058.530 seconds

// This should take roughly double the time 
print "testing...";
for mat in [L12a[j] : j in good_idxs] do
  test_canonical(mat);
end for;

