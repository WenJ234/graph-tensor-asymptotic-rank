"""Verify the five-cycle upper bound over exact rational numbers.

Use: python verify_c5_exact.py [c5_certificate.json]
Input coordinates are the ten distances between five sites in chord order.
No numerical solver, optional packages or internet access are required.
"""
import argparse
import json
from fractions import Fraction
from itertools import combinations
from pathlib import Path

PAIRS = list(combinations(range(5), 2))
INDEX = {pair: i for i, pair in enumerate(PAIRS)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ix(i, j):
    return INDEX[tuple(sorted((i % 5, j % 5)))]


def quad_edges(a, b, c, d):
    return [ix(i, j) for i, j in [(a,b), (c,d), (a,c), (b,d), (a,d), (b,c)]]


QUADS = []
for a, b, c, d in combinations(range(5), 4):
    QUADS.extend([quad_edges(a,b,c,d), quad_edges(a,c,b,d), quad_edges(a,d,b,c)])
SIDES = [ix(i, i+1) for i in range(5)]
DIAGS = [ix(i, i+2) for i in range(5)]


def local_tests(center):
    """Each triple (i,j,k) asks whether 3*(distance[i]+distance[j]) >= 4*distance[k]."""
    a0, a1, b0, b1, c = [(center+i) % 5 for i in (1,2,3,4,0)]
    tests = []
    for x, y, b in [(a0,a1,b0), (a0,a1,b1), (b1,b0,a1)]:
        for k in (c,b):
            tests.append([ix(x,k), ix(y,k), ix(b,c)])
    return tests


def inequality(key, lo, hi):
    """Return the sparse left side and constant of an inequality M*d <= rhs."""
    op, *args = key
    require(all(type(i) is int for i in args), "non-integer rule parameter")
    if op == "tri":
        i, j, k = args
        require(len({i,j,k}) == 3 and all(0 <= v < 5 for v in args), "invalid triangle")
        return [(ix(i,k),1), (ix(i,j),-1), (ix(j,k),-1)], 0
    if op == "sym":
        i, j = args
        require((i == 0 and j in (1,2,3,4)) or (i == 1 and j == 4), "invalid symmetry")
        return [(SIDES[i],1), (SIDES[j],-1)], 0
    if op == "cp":
        require(len(args) == 5 and min(args) >= 0, "invalid copositive test")
        return [(e, 4*args[i]*args[j]) for e, (i,j) in enumerate(PAIRS)], sum(args)**2
    if op == "pt":
        q, i, j, k = args
        require(0 <= q < 15 and all(v in (0,1) for v in (i,j,k)), "invalid Ptolemy test")
        a, b, c, d, e, f = QUADS[q]
        ends = (lo, hi)
        # Lower linear bound on ab, upper linear bounds on cd and ef.
        va, vb = ends[i][a], ends[i][b]
        vc, vd = ends[j][c], ends[1-j][d]
        ve, vf = ends[k][e], ends[1-k][f]
        return [(a,vb), (b,va), (c,-vd), (d,-vc), (e,-vf), (f,-ve)], va*vb-vc*vd-ve*vf
    if op == "target":
        require(not args, "invalid objective row")
        return [(i,-12) for i in DIAGS], -49
    if op == "outside":
        center, test = args
        require(0 <= center < 5 and 0 <= test < 6, "invalid local test")
        x, y, z = local_tests(center)[test]
        return [(x,3), (y,3), (z,-4)], 0
    raise ValueError("unknown rule: " + op)


def verify(document):
    rules = document["rules"]
    counts = [0, 0, 0]

    def contradiction(terms, lo, hi, allowed_exception=None):
        total = [Fraction(0)]*10
        right = Fraction(0)
        for idx, weight in terms:
            require(type(idx) is int and 0 <= idx < len(rules), "invalid rule index")
            require(type(weight) is int and weight > 0, "invalid multiplier")
            rule = rules[idx]
            if rule[0] == "outside":
                require(list(rule) == allowed_exception, "unauthorized local hypothesis")
            entries, rhs = inequality(rule, lo, hi)
            for i, value in entries:
                total[i] += weight*value
            right += weight*rhs
        left_min = sum(v*(lo[i] if v >= 0 else hi[i]) for i, v in enumerate(total))
        require(left_min > right, "combination does not prove a strict contradiction")

    def visit(node, lo, hi):
        op, arg, *rest = node
        if op == "split":
            require(type(arg) is int and 0 <= arg < 10 and len(rest) == 2, "invalid split")
            mid = (lo[arg]+hi[arg])/2
            right_lo, left_hi = list(lo), list(hi)
            right_lo[arg] = left_hi[arg] = mid
            counts[0] += 1
            visit(rest[0], lo, left_hi)
            visit(rest[1], right_lo, hi)
        elif op == "empty":
            require(not rest, "invalid exclusion leaf")
            contradiction(arg, lo, hi)
            counts[1] += 1
        elif op == "local":
            require(type(arg) is int and 0 <= arg < 5 and len(rest) == 1 and len(rest[0]) == 6,
                    "a local leaf needs six certificates for the same center")
            for t, terms in enumerate(rest[0]):
                contradiction(terms, lo, hi, ["outside", arg, t])
            counts[2] += 1
        else:
            raise ValueError("unknown node: " + op)

    visit(document["tree"], [Fraction(0)]*10, [Fraction(1)]*10)
    return counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("c5_certificate.json"))
    path = parser.parse_args().certificate
    counts = verify(json.loads(path.read_text(encoding="ascii")))
    print("Exact rational certificate verified. Splits: %d, excluded boxes: %d, local boxes: %d." % tuple(counts))
    print("Upper bound for log2 asymptotic rank: 49/12.")
