import math
from fractions import Fraction

import pytest

import probability_theory_chebyshev_vs_exact as ex


def test_tail_probability_small_cases():
    # n = 2: |k/2 - 1/2| >= 1/2 exactly for k = 0, 2.
    assert ex.tail_probability(2, Fraction(1, 2)) == Fraction(1, 2)
    # eps = 0 includes every outcome.
    assert ex.tail_probability(7, 0) == 1
    # n = 10, eps = 0.05: everything except k = 5.
    assert ex.tail_probability(10, "0.05") == 1 - Fraction(math.comb(10, 5), 2 ** 10)
    with pytest.raises(ValueError):
        ex.tail_probability(0, "0.1")


def test_tail_matches_brute_force_sum():
    n, eps = 40, Fraction(1, 10)
    brute = sum(Fraction(math.comb(n, k), 2 ** n) for k in range(n + 1)
                if abs(Fraction(k, n) - Fraction(1, 2)) >= eps)
    assert ex.tail_probability(n, eps) == brute


@pytest.mark.parametrize("n", [10, 100, 1000, 10000])
def test_bounds_are_valid(n):
    eps = Fraction(1, 20)
    exact = float(ex.tail_probability(n, eps))
    assert exact <= ex.chebyshev_bound(n, eps)
    assert exact <= ex.hoeffding_bound(n, eps)


def test_normal_approximation_is_close_for_moderate_n():
    eps = Fraction(1, 20)
    exact = float(ex.tail_probability(100, eps))
    assert abs(ex.normal_approximation(100, eps) - exact) < 0.005
    exact = float(ex.tail_probability(1000, eps))
    assert abs(ex.normal_approximation(1000, eps) / exact - 1) < 0.05


def test_chebyshev_formula():
    assert ex.chebyshev_bound(100, Fraction(1, 20)) == pytest.approx(1.0)
    assert ex.hoeffding_bound(0, 0.3) == 2


@pytest.mark.parametrize("k", [1, 2, 3, 10])
def test_three_point_distribution_attains_bound(k):
    variance, prob, bound = ex.three_point_check(k)
    assert variance == 1
    assert prob == bound == Fraction(1, k * k)


def test_three_point_rejects_small_k():
    with pytest.raises(ValueError):
        ex.three_point_check(Fraction(1, 2))
