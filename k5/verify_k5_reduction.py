"""Check the K5 restriction to a rectangular matrix multiplication tensor.

Run with Python 3 using only the standard library. Vertices 1,2 form group A,
vertices 3,4 form group B, and vertex 5 is group C. The checks compare all
coefficients for q=2 and q=3. For odd orders 3 through 21 they count
edge bundles and evaluate the rectangular exponent exactly, taking the
formula itself as a mathematical input.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product


VERTICES = (1, 2, 3, 4, 5)
EDGES = tuple(combinations(VERTICES, 2))
INCIDENT = {
    vertex: tuple(i for i, edge in enumerate(EDGES) if vertex in edge)
    for vertex in VERTICES
}


def encode(digits, q):
    index = 0
    for digit in digits:
        index = q * index + digit
    return index


def project(local, q):
    # At each vertex the four coordinates are in increasing neighbor order.
    one, two, three, four, five = local
    if one[0] or two[0] or three[2] or four[2]:
        return None  # Apply the 0-coordinate functional to each end of 12,34.

    # For AB use edge order 13,14,23,24 independently at each end.
    a = (encode((one[1], one[2], two[1], two[2]), q),
         encode((one[3], two[3]), q))
    b = (encode((three[0], four[0], three[1], four[1]), q),
         encode((three[3], four[3]), q))
    c = (encode(five[:2], q), encode(five[2:], q))
    return a, b, c


def check_restriction(q):
    observed = Counter()
    total = 0
    for labels in product(range(q), repeat=len(EDGES)):
        local = tuple(tuple(labels[i] for i in INCIDENT[v]) for v in VERTICES)
        image = project(local, q)
        if image is not None:
            observed[image] += 1
        total += 1

    # Build the comparison tensor independently from its three matrix indices.
    expected = {((u, v), (u, w), (v, w)): 1
                for u, v, w in product(range(q**4), range(q**2), range(q**2))}
    if dict(observed) != expected or total != q**10:
        raise AssertionError(f"Restriction failed at q={q}")
    print(f"q={q}: {total} K5 terms, {len(observed)} projected entries, "
          f"all coefficients equal to 1; rectangular support matches.")


def rectangular_exponent(widths):
    x, y, z = sorted(widths, reverse=True)
    excess = max(0, (x + y) * z - x * y)
    return x + y + Fraction(excess**2, 4 * x * y * z)


def check_odd_orders():
    for m in range(1, 11):
        groups = ["A"] * m + ["B"] * m + ["C"]
        counts = Counter(combinations(groups, 2))
        widths = (counts["A", "B"], counts["A", "C"], counts["B", "C"])
        internal = counts["A", "A"] + counts["B", "B"]
        if widths != (m * m, m, m) or internal != m * (m - 1):
            raise AssertionError(f"Incorrect edge counts for m={m}: {counts}")
        order = 2 * m + 1
        exponent = rectangular_exponent(widths)
        if exponent != Fraction(order**2, 4):
            raise AssertionError(f"Incorrect exponent for K{order}: {exponent}")
        print(f"K{order}: widths {widths}, internal edges {internal}, exponent {exponent}")


if __name__ == "__main__":
    for dimension in (2, 3):
        check_restriction(dimension)
    check_odd_orders()
