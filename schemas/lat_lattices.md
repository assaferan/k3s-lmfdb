Table name: `lat_lattices`

This table stores lattices (free Z-modules with a nondegenerate symmetric inner product) up to isomorphism.

Label: `dimension.signature.determinant.genus_spec.tiebreaker` where

- `genus_spec` is

  - ommitted if determinant is 1 and signature is not a multiple of 8
  - 0 for the even lattice and 1 for the odd in the case that determinant is 1 and signature is a multiple of 8
  - otherwise, for each p with p^2|determinant, we give the concatenated dimensions of the p,p^2,p^3... blocks in the Jordan decomposition (using lower case letters and then upper case letters if these dimensions are larger than 9; we separate different primes with periods.  Finally, we encode the rest of the genus information (sign, scale, oddity etc) into a single integer as described below, and append it to the Jordan information.  This integer will be even if the genus is even and odd if the genus is odd.
  - Label is in the format r.s.d.j_1.j_2....j_k.x, where
    - r is the rank of the lattice
    - s is n_plus, the number of 1s in the diagonalization over R.
    - d is the absolute value of the determinant
    - If p_1, ... , p_k are the primes whose squares divide `2*d` `(p_i^2 | 2*d)`, then
    j_1,...,j_k are corresponding rank decompositions of their Jordan forms, omitting the first, encoded in base 62 (digits 0-9, then lowercase a-z then uppercase A-Z)
    For example, if the pairs of (valuation, rank) appearing in the decomposition are (3, 1), (4,10), (6,37), it will be encoded as 01a0B (the 0s come from the fact that the rank at valuations 2 and 5 are 0).
    - The last component of the label, x, is a hexadecimal string whose bits represent the local data.
    - Let n_2 be the number of non-zero blocks in the Jordan decomposition at 2.
    - The least n_2 bits specify the types (I or II) of the non-zero blocks at 2.
    - From these, once can deduce the compartments and trains in the local symbol at 2, let c, t be their numbers.
    - The next 3*c bits represent the oddities of the compartments, with every 3 bits giving an oddity mod 8.
    - The next t bits represent the signs of the trains.
    - Finally, for every other prime p dividing d, in increasing order, if there are n_p non-zero blocks in the Jordan decomposition at p, we add n_p bits representing the signs of these blocks.
  - For the tiebreaker, we use lexicographic sorting by canonical Gram matrix for definite lattices.  For indefinite lattices, a tiebreaker is only needed in rank 2 or 3 (in rank 3 spinor genera provide a complete invariant).

| Column | Type | Description |
| --- | --- | --- |
| [aut_size](https://beta.lmfdb.org/knowledge/show/lattice.group_order) | numeric | size of automorphism group |
| aut_label | text | label for the automorphism group as an abstract group |
| [rank](https://beta.lmfdb.org/knowledge/show/lattice.dimension) | smallint | the rank of the lattice |
| signature | smallint | the number of positive diagonal entries over R, so that a positive definite lattice has signature equal to dimension |
| [det](https://beta.lmfdb.org/knowledge/show/lattice.determinant) | bigint | determinant of Gram matrix |
| disc | bigint | the discriminant (close to the determinant, but off by a factor of 2 in some cases) |
| [class_number](https://beta.lmfdb.org/knowledge/show/lattice.class_number) | smallint | size of the genus |
| [density](https://beta.lmfdb.org/knowledge/show/lattice.density) | numeric | center density of the lattice centered sphere packing (only for definite lattices) |
| [hermite](https://beta.lmfdb.org/knowledge/show/lattice.hermite_number) | numeric | Hermite number (only for definite lattices) |
| [kissing](https://beta.lmfdb.org/knowledge/show/lattice.kissing) | bigint | kissing number (only for definite lattices) |
| [level](https://beta.lmfdb.org/knowledge/show/lattice.level) | bigint | level of lattice |
| [minimum](https://beta.lmfdb.org/knowledge/show/lattice.minimal_vector) | integer | length of shortest vector (only for definite lattices) |
| name | text | a string like "E8", often null |
| [theta_series](https://beta.lmfdb.org/knowledge/show/lattice.theta) | numeric[] | a vector, counting the number of representations of n (odd) or 2n (even) |
| [gram](https://beta.lmfdb.org/knowledge/show/lattice.gram) | integer[] | A list of human-preferred gram matrices other than the canonical Gram matrix; often there will only be zero or one, but for E8 for example we want to include multiple ones |
| [canonical_gram] | integer[] | Canonical form for the Gram matrix; currently only available for definite lattices |
| [label](https://beta.lmfdb.org/Lattice/Labels) | text | We're changing the label; see above |
| [genus_label](https://beta.lmfdb.org/Lattice/Labels) | text | The part of the label that is constant across a genus |
| conway_symbol | text | the Conway symbol for the genus |
| pneighbors | jsonb | a dictionary with primes as keys and a list of labels as values (the p-neighbors) |
| discriminant_group_invs | integer[] | Smith-style invariants for the discriminant group |
| festi_veniani_index | integer | the index of the lattice automorphism group within the automorphism group of the discriminant group |
| is_even | boolean | whether the lattice is even |
| dual_label | text | the label for the minimal integral scaling of the dual lattice (may be null if the discriminant is too large) |
| dual_theta_series | numeric[] | the theta series of the dual lattice |
| dual_hermite | numeric | the Hermite number of the dual lattice (only for definite lattices) |
| dual_kissing | bigint | the kissing number of the dual lattice (only for definite lattices) |
| dual_density | numeric | the center density of the dual lattice (only for definite lattices) |
| dual_det | bigint | the determinant of the dual lattice |
| dual_conway | text | the Conway symbol for the dual lattice |
| is_universal | boolean | whether the lattice represents all positive integers |
| is_indecomposable | boolean | whether the lattice is (orthogonally) indecomposable |
| is_additively_indecomposable | boolean | whether the lattice is additively indecomposable |
| orthogonal_factors | text[] | the orthogonal decomposition of the lattice (given as a duplicate-free list of lattice labels, sorted in reverse by multiplicity, then by label) |
| orthogonal_multiplicities | smallint[] | multiplicies of the lattices in the orthogonal decomposition (a list of integers of the same length as orthogonal_factors, in a corresponding order) |
| tensor_decompositions | jsonb | A list of lists of pairs.  The overall list contains different decompositions as a tensor product; the first entry of each pair is a label and the second a multiplicity. |
| is_tensor_product | boolean | whether this lattice has a nontrivial decomposition as a tensor product |
| root_sublattice | text | the label for the root sublattice |
| root_complement | text | the label for the orthogonal complement of the root sublattice |
| even_sublattice | text | the label for the sublattice generated by vectors of even norm |
| even_complement | text | the label for the orthogonal complement of the even ublattice |
| norm1_sublattice | text | the label for the sublattice generated by vectors of norm 1 |
| norm1_complement | text | the label for the complement of the norm 1 sublattice |
| Zn_complement | text | the orthogonal complement of the maximal sublattice whose Gram matrix is diagonal |