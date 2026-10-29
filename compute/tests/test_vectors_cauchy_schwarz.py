import itertools
import math

import vectors_cauchy_schwarz as cs


def test_dot_and_cross_basics():
    e1, e2, e3 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    assert cs.dot(e1, e2) == 0 and cs.dot(e1, e1) == 1
    assert cs.cross(e1, e2) == e3 and cs.cross(e2, e1) == (0, 0, -1)
    u, v = (1, 2, 3), (4, 5, 6)
    w = cs.cross(u, v)
    assert cs.dot(w, u) == 0 and cs.dot(w, v) == 0  # cross product is perpendicular


def test_parallel_and_same_direction():
    assert cs.is_parallel((1, 2, -1), (-2, -4, 2))
    assert not cs.same_direction((1, 2, -1), (-2, -4, 2))
    assert cs.same_direction((1, 2, -1), (2, 4, -2))
    assert cs.is_parallel((0, 0, 0), (3, 1, 4))
    assert not cs.is_parallel((1, 0, 0), (1, 1, 0))


def test_triangle_holds_matches_floating_point():
    for u in itertools.product(range(-2, 3), repeat=3):
        for v in [(1, 1, 0), (-2, 1, 2), (0, 0, 0), (2, 2, 0)]:
            holds, equality = cs.triangle_holds(u, v)
            assert holds
            lhs = math.dist((0, 0, 0), tuple(a + b for a, b in zip(u, v)))
            rhs = math.dist((0, 0, 0), u) + math.dist((0, 0, 0), v)
            assert lhs <= rhs + 1e-12
            assert equality == (abs(lhs - rhs) < 1e-12)


def test_lagrange_identity_on_random_like_examples():
    for u, v in [((3, -1, 4), (1, 5, -9)), ((2, 6, 5), (3, 5, 8)), ((10, 0, -7), (0, 0, 0))]:
        lhs = cs.dot(u, u) * cs.dot(v, v) - cs.dot(u, v) ** 2
        assert lhs == cs.dot(cs.cross(u, v), cs.cross(u, v)) >= 0


def test_equality_cases_are_parallel_pairs():
    grid = list(itertools.product(range(-1, 2), repeat=3))
    for u in grid:
        for v in grid:
            equal = cs.dot(u, v) ** 2 == cs.dot(u, u) * cs.dot(v, v)
            assert equal == cs.is_parallel(u, v)
