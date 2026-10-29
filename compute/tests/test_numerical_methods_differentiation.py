import math

import pytest

import numerical_methods_differentiation as nd


def test_difference_quotients_exact_for_polynomials():
    assert nd.forward_difference(lambda x: 3 * x + 1, 2.0, 0.5) == 3.0
    assert math.isclose(nd.central_difference(lambda x: x * x, 3.0, 0.25), 6.0)


def test_v_shape_of_forward_difference():
    errs = {k: abs(nd.forward_difference(math.sin, 1.0, 10.0 ** -k) - math.cos(1.0))
            for k in range(1, 15)}
    best = min(errs, key=errs.get)
    assert 6 <= best <= 10  # near sqrt(u) = 1e-8
    assert errs[14] > errs[best] * 100


def test_quadrature_rules_exactness():
    assert math.isclose(nd.trapezoid(lambda x: 2 * x + 1, 0, 3, 5), 12.0)
    assert math.isclose(nd.simpson(lambda x: x ** 3, 0, 2, 2), 4.0)
    with pytest.raises(ValueError):
        nd.simpson(math.sin, 0, 1, 3)


def test_bessel_and_periodic_trapezoid():
    assert math.isclose(nd.bessel_i0(1.0), 1.2660658777520082, rel_tol=1e-14)
    exact = 2 * math.pi * nd.bessel_i0(1.0)
    err16 = abs(nd.trapezoid(lambda t: math.exp(math.cos(t)), 0, 2 * math.pi, 16) - exact)
    assert err16 < 1e-13


def test_sqrt_rate_is_one_and_a_half():
    e1 = abs(nd.simpson(math.sqrt, 0, 1, 256) - 2 / 3)
    e2 = abs(nd.simpson(math.sqrt, 0, 1, 1024) - 2 / 3)
    assert abs(math.log(e1 / e2, 4) - 1.5) < 0.05
