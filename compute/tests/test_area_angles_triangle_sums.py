import math
import random

import area_angles_triangle_sums as ts


def test_angle_at_known_values():
    assert math.isclose(ts.angle_at((0, 0), (1, 0), (0, 1)), 90.0)
    assert math.isclose(ts.angle_at((0, 0), (1, 0), (1, 1)), 45.0)
    assert math.isclose(ts.angle_at((0, 0), (1, 0), (-1, 0)), 180.0)
    assert math.isclose(ts.angle_at((0, 0), (2, 0), (5, 0)), 0.0, abs_tol=1e-9)


def test_longer_arms_do_not_change_the_angle():
    base = ts.angle_at((1, 1), (4, 2), (2, 3))
    for k in (2, 7, 1000):
        stretched = ts.angle_at((1, 1), (1 + 3 * k, 1 + k), (1 + k, 1 + 2 * k))
        assert math.isclose(base, stretched, rel_tol=1e-12)


def test_triangle_sums_are_180():
    rng = random.Random(7)
    for t in ts.random_triangles(rng, 200):
        assert abs(sum(ts.triangle_angles(*t)) - 180) < 1e-9
    assert math.isclose(sum(ts.triangle_angles((0, 0), (4, 0), (0, 3))), 180.0)


def test_quadrilateral_sums_are_360():
    rng = random.Random(8)
    for q in ts.random_convex_quads(rng, 100):
        assert ts.is_convex(q)
        total = sum(ts.angle_at(q[i], q[i - 1], q[(i + 1) % 4]) for i in range(4))
        assert abs(total - 360) < 1e-9


def test_convexity_check():
    assert ts.is_convex([(0, 0), (2, 0), (2, 2), (0, 2)])
    assert not ts.is_convex([(0, 0), (2, 0), (1, 1), (0, 2)])  # dented
    assert not ts.is_convex([(0, 0), (2, 2), (2, 0), (0, 2)])  # crossed


def test_exact_kind_agrees_with_measured_angles():
    assert ts.kind((0, 0), (4, 0), (0, 3)) == "right"
    assert ts.kind((0, 0), (4, 0), (2, 3)) == "acute"
    assert ts.kind((0, 0), (4, 0), (5, 1)) == "obtuse"
    rng = random.Random(9)
    for t in ts.random_triangles(rng, 300):
        biggest = max(ts.triangle_angles(*t))
        k = ts.kind(*t)
        if k == "right":
            assert math.isclose(biggest, 90.0, abs_tol=1e-9)
        elif k == "obtuse":
            assert biggest > 90
        else:
            assert biggest < 90


def test_random_triangles_are_not_flat():
    rng = random.Random(10)
    for a, b, c in ts.random_triangles(rng, 100):
        assert ts.cross(a, b, c) != 0
