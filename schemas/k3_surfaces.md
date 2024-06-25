Name: `k3_surfaces`

This table stores unpolarized K3 surfaces, up to isomorphism of varieties.  The central tool for doing so is the period, represented as a vector of complex numbers of length k (the rank of the transcendental lattice), together with an embedding of the transcendental lattice into II_{3,19}.

Note: every period must have a model associated to it, stored in the `k3_polarized` table.  This is required in order to provide an exact object underlying the given approximation.

| Column | Type | Description |
| --- | --- | --- |
| label | text | Label is LAT.isog.n, where LAT is the lattice label for the Picard lattice, isog is a counter enumerating isogeny classes ordered just by when the isogeny class was first added to the database (encoded using a lower case Cremona letter code) and n is a positive integer counter based on when each curve within an isogeny class was added |
| isogeny_class | text | Label for the isogeny class, which is LAT.isog |
| picard_lattice | text | label for Pic(X) as a lattice (and thus an entry in k3_families) |
| transcendental_lattice | text | label for the trancendental lattice (rank k) |
| transcendental_embedding | numeric[] | k by 22 integer matrix giving the embedding of T into II_{3,19} |
| period_re | numeric[] | length k vector of real parts of the periods (completely correct up to double precision) |
| period_im | numeric[] | length k vector of imaginary parts of the periods (completely correct up to double precision) |
| bit_precision | smallint | minimum of -log_2 of the radii of balls of uncertainty for periods |
| period_minpolys | numeric[] | rank x rank matrix of minpolys/ Galois module??? |
| galois_kernel | text | label for the stem field for the kernel of the Galois representation |
| endomorphism_field_dim | smallint | dimension of End_Hodge(T) |
| endomorphism_field_coeffs | numeric[] | polredabs coefficients for End_Hodge(T) |
| endomorphism_field_label | text | label for the End_Hodge(T) |
| has_rm | boolean | whether End_Hodge(T) is totally real |
| endomorphism_rank | smallint | the dimension of T as a End_Hodge(T) vector space |
| automorphism_group | jsonb | generators: 22x22 integral matrices inside Aut(II_{3,19}) that preserve the period up to scaling; maybe also record the scalars, which are algebraic numbers |
| picard_rank_upper_bound | smallint | certified upper bounds for the Picard rank |
| picard_lower_bound | text | label for a lattice certified to be contained within Pic(X) |
| picard_rank_certified | boolean | upper and lower rank bounds agree |
| picard_certified | boolean | upper and lower bounds agree (possible that the ranks agree but there could be a finite-index problem) |
| algebraic_brauer_group | bigint[] | The algebraic Brauer group of the K3 surface: Br_1(X)/Br(Q) where Br_1(X) = ker(Br(X) -> Br(Xbar)) |
| transcendental_brauer_group: Br(Xbar)/Br_1(X) |
