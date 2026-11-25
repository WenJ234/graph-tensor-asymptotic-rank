"""Check a five-cycle geometry certificate using integer arithmetic on every corner.

Run: python verify_certificate_independent.py c5_certificate.json
Python 3.8+; no optional libraries. Row slacks are nonnegative for feasible
points. A nonnegative combination strictly negative everywhere is a contradiction.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path


PAIRS = tuple(combinations(range(5), 2))
TEN = range(10)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def distance(i, j):
    return PAIRS.index(tuple(sorted((i % 5, j % 5))))


SIDES = tuple(distance(i, i + 1) for i in range(5))
CHORDS = tuple(distance(i, i + 2) for i in range(5))


def depth(node):
    if node[0] == "split":
        return 1 + max(depth(node[2]), depth(node[3]))
    return 0


def slack(rule, box, unit):
    """Return the row's slack times unit**2, as a function on the integer grid."""
    tag, *a = rule
    check(all(type(x) is int for x in a), "integer parameters required")
    if tag == "cp":
        check(len(a) == 5 and min(a) >= 0, "invalid copositive weights")
        coeff = [4 * unit * a[i] * a[j] for i, j in PAIRS]
        limit = (unit * sum(a)) ** 2
        return lambda x: limit - sum(c * t for c, t in zip(coeff, x))
    if tag == "target":
        check(not a, "invalid target")
        return lambda x: unit * (12 * sum(x[j] for j in CHORDS) - 49 * unit)
    if tag == "sym":
        i, j = a
        check((i == 0 and j in range(1, 5)) or (i, j) == (1, 4), "invalid symmetry")
        return lambda x: unit * (x[SIDES[j]] - x[SIDES[i]])
    if tag == "tri":
        i, j, k = a
        check(len(set(a)) == 3 and min(a) >= 0 and max(a) < 5, "invalid triangle")
        p, q, r = distance(i, j), distance(j, k), distance(i, k)
        return lambda x: unit * (x[p] + x[q] - x[r])
    if tag == "outside":
        c, test = a
        check(c in range(5) and test in range(6), "invalid local hypothesis")
        a0, a1, b0, b1 = [(c + s) % 5 for s in range(1, 5)]
        u, v, b = [(a0, a1, b0), (a0, a1, b1), (b1, b0, a1)][test // 2]
        k = b if test % 2 else c
        p, q, r = distance(c, b), distance(u, k), distance(v, k)
        return lambda x: unit * (4 * x[p] - 3 * (x[q] + x[r]))
    check(tag == "pt", "unknown rule")
    quad, lower, upper1, upper2 = a
    check(quad in range(15) and all(t in (0, 1) for t in a[1:]), "invalid Ptolemy row")
    vertices = list(combinations(range(5), 4))[quad // 3]
    left = vertices[0]
    partner = vertices[1 + quad % 3]
    others = [v for v in vertices if v not in (left, partner)]
    u, v = others

    def plane(e, f, side_e, side_f):
        p, q = distance(*e), distance(*f)
        h, k = box[p][side_e], box[q][side_f]
        return lambda x: x[p] * k + x[q] * h - h * k

    # xy - (xk + yh - hk) = (x-h)(y-k). Choosing opposite endpoints
    # gives an upper bound; choosing the same endpoint gives a lower bound.
    lhs = plane((left, partner), (u, v), lower, lower)
    rhs1 = plane((left, u), (partner, v), upper1, 1 - upper1)
    rhs2 = plane((left, v), (partner, u), upper2, 1 - upper2)
    return lambda x: rhs1(x) + rhs2(x) - lhs(x)


def verify(document):
    rules = document["rules"]
    tree = document["tree"]
    maximum_depth = depth(tree)
    unit = 2 ** maximum_depth
    counts = Counter()
    leaf_depths = Counter()
    centers = Counter()
    used = Counter()

    def contradiction(box, terms, path, hypothesis=None):
        check(type(terms) is list and terms, "missing contradiction")
        summands = []
        for rule_id, multiplier in terms:
            check(type(rule_id) is int and 0 <= rule_id < len(rules), "invalid rule reference")
            check(type(multiplier) is int and multiplier > 0, "invalid multiplier")
            rule = rules[rule_id]
            check(rule[0] != "outside" or rule == hypothesis, "wrong local hypothesis")
            summands.append((multiplier, slack(rule, box, unit)))
            used[rule_id] += 1
        # Affine functions achieve their extrema at corners. Checking all
        # 1024 corners keeps this verification independent of LP row reduction.
        for point in product(*box):
            check(sum(w * f(point) for w, f in summands) < 0, "uncertified leaf " + path)
        counts["contradictions"] += 1
        counts["corners"] += 2 ** len(box)

    def visit(node, box, path):
        tag, argument, *children = node
        counts[tag] += 1
        if tag == "split":
            check(type(argument) is int and argument in TEN and len(children) == 2, "invalid split")
            low, high = box[argument]
            check((low + high) % 2 == 0, "midpoint falls outside integer grid")
            midpoint = (low + high) // 2
            for child, interval, step in zip(children, [(low, midpoint), (midpoint, high)], "LR"):
                new_box = list(box)
                new_box[argument] = interval
                visit(child, new_box, path + step)
            return
        leaf_depths[len(path)] += 1
        if tag == "empty":
            check(not children, "extra data on an exclusion leaf")
            contradiction(box, argument, path)
            return
        check(tag == "local" and type(argument) is int and argument in range(5), "invalid local leaf")
        check(len(children) == 1 and len(children[0]) == 6, "six local exclusions required")
        centers[argument] += 1
        for test, terms in enumerate(children[0]):
            contradiction(box, terms, path, ["outside", argument, test])

    visit(tree, [(0, unit)] * 10, "")
    print("splits, empty leaves, local leaves:", *[counts[t] for t in ("split", "empty", "local")])
    print("Farkas combinations, corner evaluations:", counts["contradictions"], counts["corners"])
    print("maximum depth:", maximum_depth, "| leaf counts by depth:", dict(sorted(leaf_depths.items())))
    print("local leaves by center:", dict(sorted(centers.items())))
    print("distinct rows used:", len(used), "| row appearances:", sum(used.values()))
    kinds = Counter(rules[i][0] for i in used)
    print("distinct rows by family:", dict(sorted(kinds.items())))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    data = parser.parse_args().certificate.read_bytes()
    verify(json.loads(data))
    print("certificate sha256:", sha256(data).hexdigest())
