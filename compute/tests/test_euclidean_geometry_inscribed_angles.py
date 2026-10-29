import math
import random

import pytest

import euclidean_geometry_inscribed_angles as ia


def test_angle_at_known_values():
    assert ia.angle_at((1, 0), (0, 0), (0, 1)) == pytest.approx(90)
    assert ia.angle_at((1, 0), (0, 0), (1, 1)) == pytest.approx(45)
    assert ia.angle_at((1, 0), (0, 0), (-1, 0)) == pytest.approx(180)
    assert ia.angle_at((2, 0), (0, 0), (5, 0)) == pytest.approx(0)
    # The angle does not depend on the order of the two outer points.
    assert ia.angle_at((3, 1), (0, 0), (-1, 2)) == pytest.approx(
        ia.angle_at((-1, 2), (0, 0), (3, 1)))


def test_angle_at_rejects_degenerate_vertex():
    with pytest.raises(ValueError):
        ia.angle_at((0, 0), (0, 0), (1, 0))


def test_point_on_circle_has_the_right_radius():
    for t in (0, 37, 90, 200, 333):
        x, y = ia.point_on_circle(t, 2.5)
        assert math.hypot(x, y) == pytest.approx(2.5)


def test_inscribed_angle_is_half_the_central_angle():
    rng = random.Random(7)
    for _ in range(50):
        s = rng.uniform(0, 360)
        width = rng.uniform(5, 175)  # a chord whose minor arc spans `width` deg
        a, b = ia.point_on_circle(s), ia.point_on_circle(s + width)
        central = ia.angle_at(a, (0, 0), b)
        assert central == pytest.approx(width)
        major = ia.arc_samples(s + width + 1, s + 359, 20, rng)
        minor = ia.arc_samples(s + 1, s + width - 1, 20, rng)
        assert ia.max_deviation(a, b, major, central / 2) < 1e-9
        assert ia.max_deviation(a, b, minor, 180 - central / 2) < 1e-9


def test_thales_and_points_off_the_circle():
    a, b = ia.point_on_circle(90), ia.point_on_circle(270)
    assert ia.max_deviation(a, b, [10, 45, -60, 80], 90) < 1e-9
    a, b = ia.point_on_circle(200), ia.point_on_circle(340)
    inside = ia.angle_at(a, ia.point_on_circle(90, 0.8), b)
    on = ia.angle_at(a, ia.point_on_circle(90, 1.0), b)
    outside = ia.angle_at(a, ia.point_on_circle(90, 1.3), b)
    assert inside > on > outside
    assert on == pytest.approx(70)


def test_arc_samples_stay_in_range_and_are_seeded():
    xs = ia.arc_samples(10, 20, 100, random.Random(1))
    assert len(xs) == 100 and all(10 <= x <= 20 for x in xs)
    assert xs == ia.arc_samples(10, 20, 100, random.Random(1))
