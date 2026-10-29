import math

import pytest

import single_variable_calculus_riemann_rates as rr


def test_rules_are_exact_where_theory_says():
    line = lambda x: 3 * x + 1
    cubic = lambda x: x**3 - 2 * x
    # Midpoint and trapezoid rules are exact for linear functions.
    assert rr.midpoint_sum(line, 0, 2, 3) == pytest.approx(8)
    assert rr.trapezoid_sum(line, 0, 2, 3) == pytest.approx(8)
    # Simpson's rule is exact for cubics.
    assert rr.simpson_sum(cubic, -1, 2, 2) == pytest.approx(15 / 4 - 3)


def test_left_sum_of_increasing_function_underestimates():
    exact = math.e - 1
    for n in [1, 5, 50]:
        assert rr.left_sum(math.exp, 0, 1, n) < exact


def test_simpson_requires_even_strips():
    with pytest.raises(ValueError):
        rr.simpson_sum(math.exp, 0, 1, 3)
    with pytest.raises(ValueError):
        rr.simpson_sum(math.exp, 0, 1, 0)


def test_observed_orders_match_theory():
    exact = math.e - 1
    ns = [8, 16, 32, 64]
    table = rr.error_table(math.exp, 0.0, 1.0, exact, ns)
    expected = {"left": 1, "midpoint": 2, "trapezoid": 2, "Simpson": 4}
    for name, p in expected.items():
        errs = table[name]
        assert rr.observed_order(errs[-2], errs[-1]) == pytest.approx(p, abs=0.05)


def test_observed_order_formula():
    assert rr.observed_order(1.0, 0.25) == pytest.approx(2)
    assert rr.observed_order(-1.0, 0.5) == pytest.approx(1)


def test_midpoint_error_is_about_minus_half_trapezoid_error():
    exact = math.e - 1
    m = rr.midpoint_sum(math.exp, 0, 1, 64) - exact
    t = rr.trapezoid_sum(math.exp, 0, 1, 64) - exact
    assert m / t == pytest.approx(-0.5, abs=1e-3)
    # Simpson with 2n strips is (2M_n + T_n)/3.
    s = rr.simpson_sum(math.exp, 0, 1, 128)
    combo = (2 * rr.midpoint_sum(math.exp, 0, 1, 64)
             + rr.trapezoid_sum(math.exp, 0, 1, 64)) / 3
    assert s == pytest.approx(combo, rel=1e-12)
