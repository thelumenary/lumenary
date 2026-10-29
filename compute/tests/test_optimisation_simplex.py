from fractions import Fraction
from itertools import combinations

import optimisation_simplex as osx


def brute_force(a, b, c):
    """Best vertex of {x >= 0, a x <= b} in 2 variables, by enumeration."""
    lines = [(row, bi) for row, bi in zip(a, b)] + [([1, 0], 0), ([0, 1], 0)]
    best = None
    for (r1, b1), (r2, b2) in combinations(lines, 2):
        det = Fraction(r1[0] * r2[1] - r1[1] * r2[0])
        if det == 0:
            continue
        x = ((b1 * r2[1] - r1[1] * b2) / det, (r1[0] * b2 - b1 * r2[0]) / det)
        if min(x) < 0 or any(osx.dot(row, x) > bi for row, bi in zip(a, b)):
            continue
        if best is None or osx.dot(c, x) > best:
            best = osx.dot(c, x)
    return best


def test_workshop_optimum():
    status, x, y, value, _ = osx.simplex(osx.A, osx.B, osx.C)
    assert status == "optimal"
    assert x == (2, 6) and value == 36
    assert y == (0, Fraction(3, 2), 1)


def test_both_rules_reach_the_same_optimum():
    for rule in ("dantzig", "bland"):
        status, x, _, value, path = osx.simplex(osx.A, osx.B, osx.C, rule)
        assert value == 36 and x == (2, 6) and path[0] == (0, 0)
    assert len(osx.simplex(osx.A, osx.B, osx.C, "dantzig")[4]) == 3
    assert len(osx.simplex(osx.A, osx.B, osx.C, "bland")[4]) == 4


def test_strong_duality_and_complementary_slackness():
    _, x, y, value, _ = osx.simplex(osx.A, osx.B, osx.C)
    assert osx.dot(osx.B, y) == osx.dot(osx.C, x) == value
    for row, bi, yi in zip(osx.A, osx.B, y):
        assert yi * (bi - osx.dot(row, x)) == 0
    for j in range(2):
        col = [row[j] for row in osx.A]
        assert osx.dot(col, y) >= osx.C[j]


def test_agrees_with_vertex_enumeration_on_other_problems():
    problems = [
        ([[1, 1], [1, 3]], [4, 6], [2, 3]),
        ([[2, 1], [1, 2], [1, 0]], [10, 8, 4], [1, 1]),
        ([[1, 2]], [5], [1, 4]),
    ]
    for a, b, c in problems:
        status, x, y, value, _ = osx.simplex(a, b, c)
        assert status == "optimal"
        assert value == brute_force(a, b, c)
        assert osx.dot(b, y) == value


def test_unbounded_detected():
    status, x, y, value, _ = osx.simplex([[1, -1]], [1], [1, 1])
    assert status == "unbounded" and x is None
