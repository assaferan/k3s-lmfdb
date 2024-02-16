Table name: `lat_lattices`

This table stores lattices (free Z-modules with a nondegenerate symmetric inner product) up to isomorphism.

Label: `dimension.signature.determinant.genus_spec.tiebreaker` where

- `genus_spec` is

  - ommitted if determinant is 1 and signature is not a multiple of 8
  - 0 for the even lattice and 1 for the odd in the case that determinant is 1 and signature is a multiple of 8
  - otherwise, for each p with p^2|determinant, we give the concatenated dimensions of the p,p^2,p^3... blocks in the Jordan decomposition (using lower case letters and then upper case letters if these dimensions are larger than 9; we separate different primes with periods.  Finally, we encode the rest of the genus information (sign, scale, oddity etc) into a single integer as described below, and append it to the Jordan information.  This integer will be even if the genus is even and odd if the genus is odd.
  - TODO for Eran: describe this encoding
  - For the tiebreaker, we use lexicographic sorting by canonical Gram matrix for definite lattices.  For indefinite lattices, a tiebreaker is only needed in rank 2 or 3 (in rank 3 spinor genera provide a complete invariant).

| Column | Description | Type |
| --- | --- | --- |
| [aut](https://beta.lmfdb.org/knowledge/show/lattice.group_order) | size of automorphism group | numeric |
| [rank](https://beta.lmfdb.org/knowledge/show/lattice.dimension) | the rank of the lattice | smallint |
| signature | the number of positive diagonal entries over R, so that a positive definite lattice has signature equal to dimension | smallint |
| [det](https://beta.lmfdb.org/knowledge/show/lattice.determinant) | determinant of Gram matrix | bigint |
| disc | the discriminant (close to the determinant, but off by a factor of 2 in some cases) | bigint |
| [class_number](https://beta.lmfdb.org/knowledge/show/lattice.class_number) | size of the genus | smallint |
| [density](https://beta.lmfdb.org/knowledge/show/lattice.density) | center density of the lattice centered sphere packing (only for definite lattices) | numeric |
| [hermite](https://beta.lmfdb.org/knowledge/show/lattice.hermite_number) | Hermite number (only for definite lattices) | numeric |
| [kissing](https://beta.lmfdb.org/knowledge/show/lattice.kissing) | kissing number (only for definite lattices) | bigint |
| [level](https://beta.lmfdb.org/knowledge/show/lattice.level) | level of lattice | bigint |
| [minimum](https://beta.lmfdb.org/knowledge/show/lattice.minimal_vector) | length of shortest vector (only for definite lattices) | integer |
| name | a string like "E8", often null | text |
| [theta_series](https://beta.lmfdb.org/knowledge/show/lattice.theta) | a vector, counting the number of representations of n (odd) or 2n (even); left null if modular form in database | numeric[] |
| [gram](https://beta.lmfdb.org/knowledge/show/lattice.gram) | Gram matrix (in canonical form, so the knowl should be updated) | integer[] |
| [label](https://beta.lmfdb.org/Lattice/Labels) | We're changing the label; see below | text |
| [genus_label](https://beta.lmfdb.org/Lattice/Labels) | The part of the label that is constant across a genus | text |
| conway_symbol | the Conway symbol for the genus | text |
| pneighbors | a dictionary with primes as keys and a list of labels as values (the p-neighbors) | jsonb |
| discriminant_group_invs | Smith-style invariants for the discriminant group | integer[] |
| festi_veniani_index | the index of the lattice automorphism group within the automorphism group of the discriminant group | integer |
| is_even | whether the lattice is even | boolean |
| dual_label | the label for the minimal integral scaling of the dual lattice (may be null if the discriminant is too large) | text |
| dual_theta_series | the theta series of the dual lattice | numeric[] |
| dual_hermite | the Hermite number of the dual lattice (only for definite lattices) | numeric |
| dual_kissing | the kissing number of the dual lattice (only for definite lattices) | bigint |
| dual_density | the center density of the dual lattice (only for definite lattices) | numeric |
| dual_det | the determinant of the dual lattice | bigint |
| dual_conway | the Conway symbol for the dual lattice | text |