// LabelPath centralises the data directory layout: folder/rank/nplus/label,
// where the label has the form rank.nplus.det.... (see create_genus_label).
assert LabelPath("lattice_basic_data", "3.3.1.1")   eq "lattice_basic_data/3/3/3.3.1.1";
assert LabelPath("shortest", "8.8.1.1.2")           eq "shortest/8/8/8.8.1.1.2";
assert LabelPath("voronoi", "4.3.25.1")             eq "voronoi/4/3/4.3.25.1";       // indefinite: rank 4, nplus 3
assert LabelPath("genera_basic", "5.2.122.66")      eq "genera_basic/5/2/5.2.122.66"; // rank 5, nplus 2
