from fractions import Fraction
import math

import pytest
import sympy

import exact_vs_numerical as ev


def test_float_sum_is_not_point_three():
    s, eq = ev.float_sum_check()
    assert s == 0.30000000000000004
    assert eq is False


def test_exact_sums_are_exact():
    assert ev.fraction_sum_check() == (Fraction(3, 10), True)
    s, eq = ev.sympy_sum_check()
    assert s == sympy.Rational(3, 10) and eq


def test_float_point_one_is_a_binary_fraction():
    assert Fraction(0.1) == Fraction(3602879701896397, 36028797018963968)
    assert Fraction(0.1) != Fraction(1, 10)


@pytest.mark.parametrize("times", [0, 1, 10])
def test_repeated_sum_loop_small(times):
    assert ev.repeated_sum_loop(0.5, times) == 0.5 * times  # 0.5 is exact in binary


def test_repeated_sums_errors_are_ordered_as_expected():
    results = ev.repeated_sums(10_000)
    err = {k: abs(Fraction(v) - 1000) for k, v in results.items()}
    assert results["Fraction(1, 10) added exactly"] == 1000
    assert isinstance(results["Fraction(1, 10) added exactly"], Fraction)
    assert results["math.fsum (correctly rounded)"] == 1000.0
    assert 0 < err["numpy.sum, float64 (pairwise)"] < err["Python loop, float64"] < 1e-9
    assert err["numpy running sum, float32"] > 1e-3


def test_fsum_hidden_excess_is_just_under_half_an_ulp():
    hidden = 10_000 * (Fraction(0.1) - Fraction(1, 10))
    assert 0 < hidden < Fraction(math.ulp(1000.0)) / 2


def test_newton_float_converges_to_sqrt2():
    xs = ev.newton_sqrt2_float(6)
    assert xs[0] == 1.0 and xs[1] == 1.5
    assert abs(xs[-1] - math.sqrt(2)) <= 2 * math.ulp(math.sqrt(2))
    assert ev.newton_sqrt2_float(0) == [1.0]


def test_newton_exact_gives_known_convergents_never_squaring_to_two():
    xs = ev.newton_sqrt2_exact(4)
    assert xs == [Fraction(1), Fraction(3, 2), Fraction(17, 12), Fraction(577, 408), Fraction(665857, 470832)]
    assert all(x * x != 2 for x in xs)
    # Each step overshoots from above (after the first) and the error shrinks quadratically.
    assert all(x * x > 2 for x in xs[1:])
    errors = [abs(x * x - 2) for x in xs]
    assert all(b < a for a, b in zip(errors, errors[1:]))


def test_sympy_sqrt2_is_exact():
    r = sympy.sqrt(2)
    assert r ** 2 == 2
    assert r.is_irrational is True
    assert str(sympy.N(r, 30)) == "1.41421356237309504880168872421"
    assert math.sqrt(2) ** 2 != 2
