import math

import pytest

import curves_surfaces_total_curvature as tc


def test_circle_curvature_is_reciprocal_radius():
    for r in (0.5, 1.0, 3.0):
        c = lambda t, r=r: (r * math.cos(t), r * math.sin(t))
        assert tc.signed_curvature(c, 1.1) == pytest.approx(1 / r, rel=1e-6)
        c3 = lambda t, r=r: (r * math.cos(t), r * math.sin(t), 0.0)
        assert tc.curvature(c3, 0.3) == pytest.approx(1 / r, rel=1e-6)


def test_turning_numbers():
    expected = {"circle": 1, "ellipse 3 x 1": 1, "limacon r=1+2cos": 2, "figure eight": 0}
    for name, k in expected.items():
        total = tc.integrate_over_period(tc.signed_curvature, tc.PLANE[name])
        assert total == pytest.approx(2 * math.pi * k, abs=1e-4)


def test_reversed_circle_turns_minus_once():
    c = lambda t: (math.cos(-t), math.sin(-t))
    total = tc.integrate_over_period(tc.signed_curvature, c)
    assert total == pytest.approx(-2 * math.pi, abs=1e-4)


def test_fenchel_and_fary_milnor():
    totals = {name: tc.integrate_over_period(tc.curvature, c) for name, c in tc.SPACE.items()}
    for name, t in totals.items():
        assert t >= 2 * math.pi - 1e-4
    assert totals["circle in a plane"] == pytest.approx(2 * math.pi, abs=1e-4)
    assert totals["tilted ellipse"] == pytest.approx(2 * math.pi, abs=1e-4)
    assert totals["bent loop (unknot)"] > 2 * math.pi + 0.1
    assert totals["trefoil knot"] > 4 * math.pi


def test_helix_curvature():
    for a, b in [(2.0, 1.0), (1.0, 3.0)]:
        assert tc.curvature(tc.helix(a, b), 0.4) == pytest.approx(a / (a * a + b * b), rel=1e-6)


def test_cross_and_norm():
    assert tc.cross((1, 0, 0), (0, 1, 0)) == (0, 0, 1)
    assert tc.norm((3, 4)) == 5
