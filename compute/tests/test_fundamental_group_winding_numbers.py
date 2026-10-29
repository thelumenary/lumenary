import cmath
import math

import pytest

import fundamental_group_winding_numbers as fw


def test_winding_of_circles():
    for turns in (-2, -1, 1, 3):
        pts = fw.sample(fw.circle(turns=turns))
        assert fw.winding_number(pts) == pytest.approx(turns, abs=1e-9)


def test_lift_is_continuous_and_starts_at_phase():
    pts = fw.sample(fw.circle(turns=2), n=400)
    angles = fw.lift_angles(pts)
    assert angles[0] == pytest.approx(0.0)
    assert all(abs(b - a) < math.pi for a, b in zip(angles, angles[1:]))
    assert angles[-1] == pytest.approx(4 * math.pi)


def test_contour_integral_matches_lift():
    loops = [fw.circle(), fw.circle(2.0, 0.5 + 0.5j), fw.circle(0.5, 2 + 0j),
             fw.circle(turns=-3)]
    for loop in loops:
        pts = fw.sample(loop)
        w = fw.winding_number(pts)
        c = fw.contour_integral(pts)
        assert abs(c.real - w) < 1e-4 and abs(c.imag) < 1e-6


def test_loop_through_centre_is_rejected():
    with pytest.raises(ValueError):
        fw.winding_number(fw.sample(fw.circle(1.0, 1 + 0j), n=4))


def test_homotopy_invariance_until_crossing():
    for s in (0.0, 0.3, 0.8, 0.95):
        assert round(fw.winding_number(fw.sample(fw.circle(1.0, complex(s, 0))))) == 1
    for s in (1.05, 1.5, 4.0):
        assert round(fw.winding_number(fw.sample(fw.circle(1.0, complex(s, 0))))) == 0


def test_cubic_roots_counted():
    roots = [-1.76929235, 0.88464618 + 0.58974281j, 0.88464618 - 0.58974281j]
    for r in roots:
        assert abs(fw.cubic(r)) < 1e-6
    for radius, inside in [(0.5, 0), (1.0, 0), (1.5, 2), (2.0, 3), (10.0, 3)]:
        pts = [fw.cubic(z) for z in fw.sample(fw.circle(radius))]
        assert round(fw.winding_number(pts)) == inside
        assert inside == sum(abs(r) < radius for r in roots)
