"""Exact finite checks for the graph tensor counterexamples. Run with Python 3.

The mathematical input is the rectangular matrix multiplication exponent from
OAI.LinearAlgebra.SpectralBooks.rectangular_exponent. This script checks its
specializations and the graph combinatorics using rational arithmetic.
"""

from fractions import Fraction
from itertools import combinations, product


def rectangular_exponent(weights):
    x, y, z = sorted(weights, reverse=True)
    if z == 0:
        return Fraction(x + y)
    correction = max(0, (x + y) * z - x * y)
    return x + y + Fraction(correction**2, 4 * x * y * z)


def grouping_weights(edges, groups):
    counts = {(0, 1): 0, (0, 2): 0, (1, 2): 0}
    for u, v in edges:
        a, b = sorted((groups[u], groups[v]))
        if a != b:
            counts[a, b] += 1
    return tuple(sorted(counts.values(), reverse=True))


def check(name, edges, groups, expected_cut, expected_weights, expected_lower):
    n = len(groups)
    maxcut = max(sum(side[u] != side[v] for u, v in edges)
                 for side in product(range(2), repeat=n))
    weights = grouping_weights(edges, groups)
    lower = rectangular_exponent(weights)
    best_grouping = max(rectangular_exponent(grouping_weights(edges, assignment))
                        for assignment in product(range(3), repeat=n))
    assert (maxcut, weights, lower) == (expected_cut, expected_weights, expected_lower)
    assert maxcut < lower == best_grouping
    print(f"{name}: MaxCut={maxcut}, weights={weights}, "
          f"three-group lower bound={lower}, gap={lower - maxcut}")


if __name__ == "__main__":
    for n in (3, 5, 7, 9):
        t = n // 2
        complete_edges = list(combinations(range(n), 2))
        check(f"K{n}", complete_edges, [0] * t + [1] * t + [2],
              t * (t + 1), (t * t, t, t), Fraction(n**2, 4))
        cycle_edges = [(i, (i + 1) % n) for i in range(n)]
        check(f"C{n}", cycle_edges, [0, 1] * t + [2],
              n - 1, (n - 2, 1, 1), n - 1 + Fraction(1, 4 * (n - 2)))
