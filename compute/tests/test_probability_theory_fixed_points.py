import math
from fractions import Fraction

import pytest

import probability_theory_fixed_points as ex


def test_counts_small_cases():
    assert ex.fixed_point_counts(0) == [0]
    assert ex.fixed_point_counts(1) == [1]
    assert sorted(ex.fixed_point_counts(3)) == [0, 0, 1, 1, 1, 3]
    with pytest.raises(ValueError):
        ex.fixed_point_counts(-1)


@pytest.mark.parametrize("n", range(2, 8))
def test_mean_and_variance_are_one(n):
    m, v = ex.mean_and_variance(ex.fixed_point_counts(n))
    assert m == 1
    assert v == 1


def test_mean_and_variance_of_simple_lists():
    assert ex.mean_and_variance([0, 2]) == (1, 1)
    assert ex.mean_and_variance([5]) == (5, 0)
    with pytest.raises(ValueError):
        ex.mean_and_variance([])


def test_derangement_numbers():
    # Derangements D_n = 1, 0, 1, 2, 9, 44, 265, 1854 for n = 0..7.
    derangements = [1, 0, 1, 2, 9, 44, 265, 1854]
    for n in range(1, 8):
        p0 = ex.distribution(ex.fixed_point_counts(n)).get(0, Fraction(0))
        assert p0 == Fraction(derangements[n], math.factorial(n))


def test_distribution_sums_to_one_and_never_n_minus_one():
    dist = ex.distribution(ex.fixed_point_counts(6))
    assert sum(dist.values()) == 1
    assert 5 not in dist  # n - 1 fixed points force the last one too
    assert dist[6] == Fraction(1, 720)
