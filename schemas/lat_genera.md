Table name: `lat_genera`

This table stores lattices (free Z-modules with a nondegenerate symmetric inner product) up to local equivalence (also refered to as the genus of the lattice).

| Column | Description | Type |
| --- | --- | --- |
| [label](https://beta.lmfdb.org/Lattice/Labels) | The part of the label that is constant across a genus | text |
| [rank](https://beta.lmfdb.org/knowledge/show/lattice.dimension) | the rank of the lattice | smallint |
| signature | the number of positive diagonal entries over R, so that a positive definite lattice has signature equal to dimension | smallint |
| [class_number](https://beta.lmfdb.org/knowledge/show/lattice.class_number) | size of the genus | smallint |
| [det](https://beta.lmfdb.org/knowledge/show/lattice.determinant) | determinant of Gram matrix | bigint |
| disc | the discriminant (close to the determinant, but off by a factor of 2 in some cases) | bigint |
| conway_symbol | the Conway symbol for the genus | text |
| [level](https://beta.lmfdb.org/knowledge/show/lattice.level) | level of lattice | bigint |
| is_even | whether the lattice is even | boolean |
| discriminant_group_invs | Smith-style invariants for the discriminant group | integer[] |
| discriminant_form | Quadratic form on the discriminant group, as a symmetric matrix | integer[] |
| adjacency_matrix | jsonb | A dictionary with primes as keys and upper-triangular-flattened p-neighbor adjaceny matrix as values |
| adjacency_polynomials | jsonb | A dictionary with primes as keys and character polynomials of adjacency matrices as values (as a list of integer coefficients) |
