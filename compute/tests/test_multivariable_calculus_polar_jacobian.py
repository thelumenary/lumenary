import math

import pytest

import multivariable_calculus_polar_jacobian as pj


def test_exact_disc_formula():
    assert pj.exact_disc(0) == 0
    assert pj.exact_disc(1) == pytest.approx(math.pi * (1 - math.exp(-1)))
    assert pj.exact_disc(10) == pytest.approx(math.pi)


def test_polar_with_jacobian_matches_exact():
    for radius in [0.5, 1, 2]:
        assert pj.polar_disc(pj.gauss2, radius) == pytest.approx(pj.exact_disc(radius), rel=1e-5)


def test_polar_without_jacobian_is_wrong():
    for radius in [0.5, 1, 2]:
        bad = pj.polar_disc(pj.gauss2, radius, jacobian=False)
        assert abs(bad - pj.exact_disc(radius)) > 0.5


def test_area_of_disc_needs_the_factor_r():
    one = lambda x, y: 1.0
    assert pj.polar_disc(one, 3, n_r=100, n_t=16) == pytest.approx(9 * math.pi)
    # Without r one gets 2 pi R instead of pi R^2.
    assert pj.polar_disc(one, 3, n_r=100, n_t=16, jacobian=False) == pytest.approx(6 * math.pi)


def test_cartesian_grid_is_close():
    assert pj.cartesian_disc(pj.gauss2, 1.0, n=200) == pytest.approx(pj.exact_disc(1.0), abs=2e-3)


def test_gaussian_line_integral():
    assert pj.gaussian_line() == pytest.approx(math.sqrt(math.pi), rel=1e-12)
    assert pj.gaussian_line() ** 2 == pytest.approx(math.pi, rel=1e-12)
