from fractions import Fraction

import pytest

import polynomials_remainder_theorem as prt


def test_synthetic_division_worked_example():
    q, r = prt.synthetic_division([2, -3, -11, 6], 3)
    assert q == [2, 3, -2]
    assert r == 0


def test_remainder_equals_value_with_fractions():
    p = [1, 0, 0, -2]
    for a in [Fraction(5, 4), Fraction(-7, 3), 0, 2]:
        _, r = prt.synthetic_division(p, a)
        assert r == prt.evaluate(p, a)
    assert prt.synthetic_division(p, Fraction(5, 4))[1] == Fraction(-3, 64)


def test_quotient_times_divisor_plus_remainder_rebuilds_p():
    p = [3, 0, -4, 1, 5]
    a = Fraction(-2, 3)
    q, r = prt.synthetic_division(p, a)
    # (x - a) * q + r, coefficients highest first
    rebuilt = [q[0]] + [q[i] - a * q[i - 1] for i in range(1, len(q))] + [r - a * q[-1]]
    assert rebuilt == p


def test_constant_polynomial_and_errors():
    assert prt.synthetic_division([7], 4) == ([], 7)
    with pytest.raises(ValueError):
        prt.synthetic_division([], 1)
    with pytest.raises(ValueError):
        prt.divisors(0)


def test_rational_root_test():
    assert prt.divisors(6) == [1, 2, 3, 6]
    cands = prt.rational_root_candidates([2, -3, -11, 6])
    assert len(cands) == 12
    assert prt.rational_roots([2, -3, -11, 6]) == [-2, Fraction(1, 2), 3]
    assert prt.rational_roots([1, 0, 0, -2]) == []
    assert prt.rational_roots([1, 0, -1]) == [-1, 1]


def test_show():
    assert prt.show([2, 3, -2]) == "2x^2 + 3x - 2"
    assert prt.show([-1, 0, 1]) == "-x^2 + 1"
    assert prt.show([1, 0]) == "x"
    assert prt.show([0]) == "0"


def test_random_check_finds_no_counterexample_and_is_deterministic():
    assert prt.random_check(300) == 0
    assert prt.random_check(300, seed=7) == 0
