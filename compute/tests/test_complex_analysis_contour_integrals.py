import cmath
import math

import pytest

import complex_analysis_contour_integrals as ex

TWO_PI_I = 2j * math.pi


def test_basic_integrals_on_unit_circle():
    assert abs(ex.circle_integral(lambda z: 1 / z) - TWO_PI_I) < 1e-12
    for n in range(0, 5):  # z^n integrates to 0 for n >= 0
        assert abs(ex.circle_integral(lambda z: z ** n)) < 1e-12
    assert abs(ex.circle_integral(lambda z: z ** -2)) < 1e-12


def test_conjugate_is_not_holomorphic():
    # On |z| = 1, conj(z) = 1/z, so the integral is 2 pi i, not 0.
    assert abs(ex.circle_integral(lambda z: z.conjugate()) - TWO_PI_I) < 1e-12
    # On |z| = 2, conj(z) = 4/z: integral 8 pi i.
    assert abs(ex.circle_integral(lambda z: z.conjugate(), 0j, 2.0) - 4 * TWO_PI_I) < 1e-10


def test_cauchy_integral_formula_and_derivatives():
    w = 0.3 - 0.2j
    v = ex.circle_integral(lambda z: cmath.exp(z) / (z - w), 0j, 1.0, 64) / TWO_PI_I
    assert abs(v - cmath.exp(w)) < 1e-12
    # f''(0)/2! for f = exp is 1/2
    v2 = ex.circle_integral(lambda z: cmath.exp(z) / z ** 3) / TWO_PI_I
    assert abs(v2 - 0.5) < 1e-12
    # A point outside the circle contributes nothing (Cauchy's theorem).
    assert abs(ex.circle_integral(lambda z: 1 / (z - 3))) < 1e-12


def test_trapezoid_error_decreases_geometrically():
    errs = [abs(ex.circle_integral(lambda z: cmath.exp(z) / (z - 0.5), n=n) / TWO_PI_I
                - math.exp(0.5)) for n in (4, 8, 16, 32)]
    assert errs == sorted(errs, reverse=True)
    assert errs[-1] < 1e-8
    with pytest.raises(ValueError):
        ex.circle_integral(lambda z: z, n=0)


def test_simpson_and_residue_values():
    assert math.isclose(ex.simpson(lambda x: x ** 3, 0, 2, 2), 4.0)
    with pytest.raises(ValueError):
        ex.simpson(lambda x: x, 0, 1, 3)
    b = ex.simpson(lambda x: math.cos(x) / (1 + x * x), -400, 400, 80000)
    assert abs(b - math.pi / math.e) < 5e-5
    a = ex.simpson(lambda x: 1 / (1 + x * x), -400, 400, 80000)
    exact_truncated = 2 * math.atan(400)
    assert abs(a - exact_truncated) < 1e-9


def test_argument_principle_counts():
    p = lambda z: z ** 5 - 3 * z + 1
    dp = lambda z: 5 * z ** 4 - 3
    assert round(ex.count_zeros(p, dp, 1.0).real) == 1
    assert round(ex.count_zeros(p, dp, 2.0).real) == 5
    assert abs(ex.count_zeros(lambda z: z ** 3, lambda z: 3 * z ** 2, 1.0) - 3) < 1e-9
