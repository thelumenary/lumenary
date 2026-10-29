import math

import pytest

import riemannian_geometry_geodesics as rg


def test_rk4_solves_harmonic_oscillator():
    rhs = lambda s: [s[1], -s[0]]
    end = rg.rk4(rhs, [0.0, 1.0], 1e-3, 1000)
    assert end[0] == pytest.approx(math.sin(1.0), abs=1e-10)


def test_distance_formulas():
    assert rg.sphere_distance((math.pi / 2, 0), (math.pi / 2, math.pi / 2)) == pytest.approx(math.pi / 2)
    assert rg.sphere_distance((0.3, 1.0), (0.3, 1.0)) == pytest.approx(0)
    # Vertical segment from (0, 1) to (0, e) has hyperbolic length 1.
    assert rg.half_plane_distance((0, 1), (0, math.e)) == pytest.approx(1)


def test_equator_is_a_geodesic_and_unit_speed_is_preserved():
    end = rg.rk4(rg.sphere_rhs, [math.pi / 2, 0.0, 0.0, 1.0], 1e-3, 2000)
    assert end[0] == pytest.approx(math.pi / 2, abs=1e-12)
    assert end[1] == pytest.approx(2.0, abs=1e-9)


@pytest.mark.parametrize("t", [0.5, 1.5, 2.5])
def test_spreading_matches_jacobi_fields(t):
    assert rg.spread("sphere", t) == pytest.approx(math.sin(t), abs=1e-4)
    assert rg.spread("half-plane", t) == pytest.approx(math.sinh(t), rel=1e-4)


def test_conjugate_point_on_sphere():
    assert rg.spread("sphere", math.pi) == pytest.approx(0, abs=1e-4)


def test_clairaut_constant_is_conserved():
    c0, worst, min_rho = rg.clairaut_run(t=10.0)
    assert worst < 1e-9
    assert min_rho >= abs(c0) - 1e-6
    assert c0 == pytest.approx(3.0 * math.cos(1.2))
