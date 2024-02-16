Table name: `lat_inclusions`

This stores inclusion relationships among lattices, up to composition with automorphisms on both the domain and the codomain.  Currently there are no completeness guarantees for this data.

| Column | Description | Type |
| --- | --- | --- |
| domain | label of the domain | text |
| codomain | label of the codomain | text |
| primitive | whether the inclusion is primitive; equivalence to quotient being torsion free and to the codomain being a direct sum of the domain and the quotient |
| quotient_invs | elementary abelian invariants of the quotient | integer[] |
| domain_rank | rank of the domain | smallint |
| codomain_rank | rank of the codomain | smallint |
| quotient_rank | rank of the quotient | smallint |
| multiplicity | the number of inclusions of this type (with given domain, codomain and quotient_invs) up to automorphism (note that this is difficult to compute, and probably not feasible when  | integer |
| images | A matrix A so that the inclusion is y = A*x in terms of the fixed bases for the domain and codomain | numeric[] |