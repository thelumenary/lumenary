import itertools
import math

import pytest

import euclidean_geometry_ssa as ssa


def brute_force_count(a_sq, c, p, q):
    """Count the positive roots of t^2 - 2ut + (c^2 - a_sq) = 0 numerically."""
    r = math.sqrt(p * p + q * q)
    u = c * p / r
    disc = u * u - (c * c - a_sq)
    if disc < -1e-9:
        return 0
    if abs(disc) <= 1e-9:
        return 1 if u > 1e-9 else 0
    roots = [u - math.sqrt(disc), u + math.sqrt(disc)]
    return sum(t > 1e-9 for t in roots)


def test_lesson_counterexample_has_two_triangles():
    assert ssa.count_triangles(10, 5, 4, 3) == 2
    assert ssa.third_sides(10, 5, 4, 3) == pytest.approx([3.0, 5.0])


def test_boundary_cases():
    # Right triangle: BC equals the height, exactly one triangle.
    assert ssa.count_triangles(36, 10, 4, 3) == 1
    # Too short to reach the line: none.
    assert ssa.count_triangles(25, 10, 4, 3) == 0
    # Isosceles: the second root is t = 0, a degenerate "triangle".
    assert ssa.count_triangles(100, 10, 4, 3) == 1
    # Right angle at A: only BC > AB works.
    assert ssa.count_triangles(25, 5, 0, 1) == 0
    assert ssa.count_triangles(26, 5, 0, 1) == 1
    # Obtuse angle at A.
    assert ssa.count_triangles(50, 10, -3, 4) == 0
    assert ssa.count_triangles(150, 10, -3, 4) == 1


def test_exact_count_matches_rule_and_floating_point():
    for (p, q), c, a in itertools.product(ssa.DIRECTIONS, range(1, 13), range(1, 13)):
        exact = ssa.count_triangles(a * a, c, p, q)
        assert exact == ssa.predicted_count(a * a, c, p, q)
        assert exact == brute_force_count(a * a, c, p, q)
        assert exact == len(ssa.third_sides(a * a, c, p, q))


def test_two_triangles_really_are_different():
    for a in (7, 8, 9):
        t1, t2 = ssa.third_sides(a * a, 10, 4, 3)
        assert t1 != pytest.approx(t2)
        # Both satisfy BC = a with B = (8, 6).
        for t in (t1, t2):
            assert math.hypot(8 - t, 6) == pytest.approx(a)


def test_invalid_input_rejected():
    with pytest.raises(ValueError):
        ssa.count_triangles(10, 5, 1, 1)  # 1 + 1 is not a perfect square
    with pytest.raises(ValueError):
        ssa.count_triangles(10, 5, 4, -3)
