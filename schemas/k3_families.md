Table name: `k3_families`

| Column    | Type    | Description    |
| ----------- | -------------- | --------------- |
| picard_lattice | text |  label of the indefinite lattice  isometric to Pic(X) |
| polarized_lattice_genus | text |  label of the genus of the positive definite lattice L in the decomposition Pic(X) = U + L.  If there is no such decomposition, this field is null |
| num_elliptic_surfaces | smallint | number of elliptic surfaces isomorphic to X |
| discriminant | integer | discriminant of Pic(X) |
| related_objects | text[] | other objects related to X (such as modular forms, etc. |
| parameter_space_ambient | text | the label of the ambient space of the parameter space as a toric variety|
| parameter_space_equations | text[] | equations describing the parameter space |
| parameter_space_description | text | description of the parameter space |
| parameter_space_dim | integer | dimension of the parameter space |
| moduli_space_dim | integer | dimension of the moduli space |
| moduli_space_unirational | boolean | whether the moduli space is unirational |
| fiber_dim | integer | dimension of the fiber to the moduli space |
| fiber_group | text | description of the automorphism group of the fiber |
| versal_family | text | The equation for a K3 surface corresponding to the generic point in the parameter space |
| specializations | text[] | picard_lattice labels for higher rank specializations |
| specialization_loci | text[] | list of lists of equations cutting out the loci where each specialization occurs |