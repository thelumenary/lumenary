import math
from fractions import Fraction

import pytest
import sympy

import intro_calculus_riemann_sums as ex

ZERO, ONE = Fraction(0), Fraction(1)


@pytest.mark.parametrize("n", [1, 2, 3, 7, 50, 333])
def test_right_sum_matches_closed_form(n):
    assert ex.riemann_sum(ex.square, ZERO, ONE, n) == ex.right_closed_form(n)


@pytest.mark.parametrize("n", [1, 5, 40])
def test_exact_errors(n):
    third = Fraction(1, 3)
    right = ex.riemann_sum(ex.square, ZERO, ONE, n, "right")
    left = ex.riemann_sum(ex.square, ZERO, ONE, n, "left")
    mid = ex.riemann_sum(ex.square, ZERO, ONE, n, "midpoint")
    assert right - third == Fraction(1, 2 * n) + Fraction(1, 6 * n * n)
    assert left - third == -Fraction(1, 2 * n) + Fraction(1, 6 * n * n)
    assert mid - third == Fraction(-1, 12 * n * n)
    assert left < third < right


def test_linear_function_midpoint_is_exact():
    f = lambda x: 3 * x + 1  # noqa: E731
    assert ex.riemann_sum(f, ZERO, Fraction(2), 5, "midpoint") == 8


def test_bad_arguments():
    with pytest.raises(ValueError):
        ex.riemann_sum(ex.square, ZERO, ONE, 0)
    with pytest.raises(ValueError):
        ex.riemann_sum(ex.square, ZERO, ONE, 3, "upper")


def test_antiderivative_and_signed_area():
    anti, area = ex.antiderivative_check()
    x = sympy.symbols("x")
    assert sympy.diff(anti, x) == x ** 2
    assert area == sympy.Rational(1, 3)
    signed = ex.riemann_sum(math.sin, 0.0, 2 * math.pi, 1000, "midpoint")
    assert abs(signed) < 1e-12
    assert math.isclose(ex.riemann_sum(math.sin, 0.0, math.pi, 1000, "midpoint"), 2, rel_tol=1e-5)
