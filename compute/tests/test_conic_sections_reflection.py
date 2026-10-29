import math
import random

import pytest

import conic_sections_reflection as cr


def test_reflect_basic_cases():
    # Mirror = the x-axis (normal (0, 1)): a downward ray bounces straight up.
    assert cr.reflect((0, -1), (0, 1)) == pytest.approx((0, 1))
    # A 45-degree ray off a horizontal mirror.
    assert cr.reflect((1, -1), (0, 2)) == pytest.approx((1, 1))
    # Reflection keeps the length of the direction.
    v = cr.reflect((3, 4), (1, 2))
    assert math.hypot(*v) == pytest.approx(5)


def test_parabola_rays_meet_at_the_focus():
    for p in (0.25, 1.0, 3.0):
        for x0 in (-7.5, -1, 0.1, 2, 10):
            assert cr.parabola_axis_crossing(p, x0) == pytest.approx(p, abs=1e-9)


def test_ellipse_hit_is_on_the_ellipse():
    a, b = 5.0, 3.0
    rng = random.Random(4)
    for _ in range(50):
        t = rng.uniform(0, 2 * math.pi)
        x, y = cr.ellipse_hit(a, b, (-4.0, 0.0), (math.cos(t), math.sin(t)))
        assert (x / a) ** 2 + (y / b) ** 2 == pytest.approx(1)


def test_ellipse_rays_pass_through_other_focus():
    a, b = 5.0, 3.0
    c = math.sqrt(a * a - b * b)
    for k in range(36):
        t = 2 * math.pi * (k + 0.25) / 36
        hit = cr.ellipse_hit(a, b, (-c, 0.0), (math.cos(t), math.sin(t)))
        out = cr.reflect((hit[0] + c, hit[1]), (hit[0] / a ** 2, hit[1] / b ** 2))
        assert cr.distance_to_line((c, 0.0), hit, out) < 1e-9


def test_distance_to_line():
    assert cr.distance_to_line((0, 5), (0, 0), (1, 0)) == pytest.approx(5)
    assert cr.distance_to_line((3, 3), (0, 0), (2, 2)) == pytest.approx(0)
