"""
Check genus.lattice_level against the definition in the LMFDB knowl
lattice.level: the smallest N with N * B(v, v) in 2Z for all v in the dual.
Run: sage -python tests/test_level.py   (from lattices/)

The pipeline used to store Sage's GenusSymbol.level(), which is the exponent
of the discriminant group; that is half the LMFDB level whenever the top-scale
2-adic block is odd (e.g. A1: 2 vs 4, I2: 1 vs 2, diag(1,3): 3 vs 6).
"""
import itertools, sys, os
sys.path.insert(0, os.getcwd())
from sage.all import matrix, ZZ, lcm  # type: ignore
from sage.quadratic_forms.genera.genus import Genus  # type: ignore
from genus import lattice_level  # type: ignore


def level_from_definition(G):
    D = G.inverse()
    N = lcm([x.denominator() for x in D.list()])
    return N if all((N * D[i, i]) % 2 == 0 for i in range(G.nrows())) else 2 * N


known = [([[2]], 4), ([[1, 0], [0, 1]], 2), ([[2, 1], [1, 2]], 3), ([[1, 0], [0, 3]], 6),
         ([[0, 1], [1, 0]], 1), ([[2, -1, 0, 0], [-1, 2, -1, 0], [0, -1, 2, -1], [0, 0, -1, 2]], 5)]
failures = []
for g, N in known:
    got = lattice_level(Genus(matrix(ZZ, g)))
    if got != N:
        failures.append((g, N, got))

count = 0
for a, b, c in itertools.product(range(-6, 7), repeat=3):
    G = matrix(ZZ, [[a, b], [b, c]])
    if G.det() == 0:
        continue
    count += 1
    if lattice_level(Genus(G)) != level_from_definition(G):
        failures.append((G.list(), level_from_definition(G), lattice_level(Genus(G))))

if failures:
    print("FAIL: %d mismatches, e.g. %s" % (len(failures), failures[:5]))
    sys.exit(1)
print("PASS: %d known levels and %d binary forms (definite and indefinite)" % (len(known), count))
