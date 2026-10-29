import math

import pytest

import real_analysis_weierstrass_function as ex


def test_value_at_zero_is_geometric_series():
    assert ex.w_at_zero() == 2.0
    assert math.isclose(ex.partial_sum(0.0, 60), 2.0)


def test_closed_form_agrees_with_direct_sum_where_floats_are_safe():
    # With b = 3 the large-k terms carry weight 2^-k, so float error in
    # cos(3^k pi h) for k > 30 stays far below the tolerance.
    for m in [1, 2, 3]:
        direct = ex.partial_sum(3.0 ** -m, 40, a=0.5, b=3)
        assert math.isclose(ex.w_at_power(m, a=0.5, b=3), direct, abs_tol=1e-9)


def test_tail_needs_odd_b():
    with pytest.raises(ValueError):
        ex.w_at_power(2, a=0.5, b=4)


def test_quotients_grow_like_ab_to_the_m():
    ratios = [ex.quotient(m) / 6.5 ** m for m in range(2, 9)]
    for r in ratios:
        assert -4.07 < r < -4.05
    # The lesson's lower bound: |D_m| >= (ab)^m (2/(1-a) - pi^2 / (2 (a b^2 - 1))).
    c = 2 / (1 - ex.A) - math.pi ** 2 / (2 * (ex.A * ex.B ** 2 - 1))
    for m in range(1, 9):
        assert abs(ex.quotient(m)) >= c * 6.5 ** m * (1 - 1e-12)


def test_partial_sum_quotients_tend_to_zero():
    values = [abs(ex.partial_quotient(m, 3)) for m in range(4, 9)]
    assert values == sorted(values, reverse=True)
    assert values[-1] < 1e-3
