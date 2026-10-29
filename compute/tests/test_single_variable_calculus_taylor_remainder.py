import math
from fractions import Fraction

import pytest

import single_variable_calculus_taylor_remainder as tr


def test_exp_taylor_exact_values():
    assert tr.exp_taylor(1, 0) == 1
    assert tr.exp_taylor(1, 3) == Fraction(8, 3)  # 1 + 1 + 1/2 + 1/6
    assert tr.exp_taylor(Fraction(1, 2), 2) == Fraction(13, 8)
    assert tr.exp_taylor(-1, 2) == Fraction(1, 2)
    with pytest.raises(ValueError):
        tr.exp_taylor(1, -1)


def test_sin_taylor_exact_values():
    assert tr.sin_taylor(1, 0) == 0
    assert tr.sin_taylor(1, 1) == 1
    assert tr.sin_taylor(1, 3) == Fraction(5, 6)  # 1 - 1/6
    assert tr.sin_taylor(1, 5) == Fraction(5, 6) + Fraction(1, 120)
    # T_n = T_(n+1) for odd n, because sin has only odd powers.
    assert tr.sin_taylor(Fraction(3, 10), 5) == tr.sin_taylor(Fraction(3, 10), 6)


@pytest.mark.parametrize("x", [1, -2, 0.5, 3])
def test_lagrange_bound_dominates_actual_error_for_exp(x):
    for n in range(1, 15):
        actual = abs(math.exp(x) - float(tr.exp_taylor(Fraction(x), n)))
        assert actual <= tr.exp_bound(x, n) * (1 + 1e-9) + 1e-15


@pytest.mark.parametrize("x", [0.3, -1.2, 2.0])
def test_lagrange_bound_dominates_actual_error_for_sin(x):
    for n in range(0, 12):
        actual = abs(math.sin(x) - float(tr.sin_taylor(Fraction(x), n)))
        assert actual <= tr.sin_bound(x, n) * (1 + 1e-9) + 1e-15


def test_errors_tend_to_zero_for_exp():
    rows = tr.error_rows(math.exp, tr.exp_taylor, tr.exp_bound, 1, [2, 6, 10])
    errors = [actual for _, actual, _ in rows]
    assert errors[0] > errors[1] > errors[2]
    assert errors[2] < 1e-7


def test_degree_for_e():
    n = tr.degree_for_e(1e-10)
    assert n == 13
    assert 3 / math.factorial(n + 1) < 1e-10 <= 3 / math.factorial(n)
    assert abs(math.e - float(tr.exp_taylor(1, n))) < 1e-10
    assert tr.degree_for_e(1) == 2  # 3/3! = 0.5 < 1 but 3/2! = 1.5 >= 1


def test_flat_function():
    assert tr.flat(0) == 0.0
    assert tr.flat(0.5) == pytest.approx(math.exp(-4))
    assert tr.flat(-0.5) == tr.flat(0.5)
    assert 0 < tr.flat(0.1) < 1e-40
    # Flatness: f(h) / h^k -> 0 for every k (checked here for k <= 10).
    for k in range(11):
        assert tr.flat(0.05) / 0.05**k < 1e-100
