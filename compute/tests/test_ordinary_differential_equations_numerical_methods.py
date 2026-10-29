import math

import pytest

import ordinary_differential_equations_numerical_methods as nm


def test_euler_on_growth_is_compound_interest():
    for n in [1, 5, 50]:
        assert nm.euler(nm.growth, 0.0, 1.0, 1.0, n) == pytest.approx((1 + 1 / n) ** n, rel=1e-12)


def test_methods_are_exact_for_constant_slope():
    f = lambda t, x: 2.0
    assert nm.euler(f, 0.0, 1.0, 3.0, 7) == pytest.approx(7.0)
    assert nm.rk4(f, 0.0, 1.0, 3.0, 7) == pytest.approx(7.0)


def test_rk4_exact_for_cubic_in_t():
    # For x' = g(t), RK4 is Simpson's rule, which is exact when g is a cubic or lower.
    f = lambda t, x: 3 * t * t
    assert nm.rk4(f, 0.0, 0.0, 2.0, 3) == pytest.approx(8.0)


def test_orders_of_convergence():
    errs_e = [nm.euler(nm.growth, 0.0, 1.0, 1.0, n) - math.e for n in (100, 200)]
    errs_r = [nm.rk4(nm.growth, 0.0, 1.0, 1.0, n) - math.e for n in (10, 20)]
    assert nm.observed_order(*errs_e) == pytest.approx(1, abs=0.05)
    assert nm.observed_order(*errs_r) == pytest.approx(4, abs=0.1)


def test_blowup_values_grow():
    v1 = nm.rk4(nm.square, 0.0, 1.0, 0.9, 900)
    v2 = nm.rk4(nm.square, 0.0, 1.0, 0.99, 990)
    assert v1 == pytest.approx(10, rel=1e-6)
    assert v2 == pytest.approx(100, rel=1e-3)


def test_non_uniqueness_is_invisible_to_numerics():
    assert nm.rk4(nm.sqrt_abs, 0.0, 0.0, 2.0, 2000) == 0.0
    assert nm.euler(nm.sqrt_abs, 0.0, 0.0, 2.0, 2000) == 0.0
    near = nm.rk4(nm.sqrt_abs, 0.0, 1e-12, 2.0, 2000)
    assert near == pytest.approx(1.0, abs=2e-3)  # follows t^2/4
