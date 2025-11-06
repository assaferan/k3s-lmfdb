import "canonical_form.m" : test_canonical, num_V;
import "tests/_L12a+.m" : L12a;
// This is still impossible because some of these lattices have
// characteristic vector sets that are too large.
// time cans := [CanonicalForm(A) : A in L12a];
nums := [num_V(ChangeRing(A,Rationals())) : A in L12a]; // takes a long while
/*
[ 484, 304, 356, 122, 276, 2556, 33252, 742, 894, 278, 308, 1868, 4544, 8256,
222, 220, 618, 1186, 13410, 742, 484, 332, 206, 58, 676, 248, 164, 197, 
886, 118, 454, 164, 240, 246, 216, 2556, 502, 820, 654, 272, 332, 240, 348, 
676, 524, 232, 146, 252, 328, 376, 228, 656, 656 ] 
*/
