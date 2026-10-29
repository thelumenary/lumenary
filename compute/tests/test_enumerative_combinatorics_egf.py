import math
from fractions import Fraction

import pytest

import enumerative_combinatorics_egf as ee


def test_bell_numbers():
    assert ee.set_partitions_egf()[:9] == [1, 1, 2, 5, 15, 52, 203, 877, 4140]


def test_involutions_and_derangements_values():
    assert ee.involutions_egf()[:8] == [1, 1, 2, 4, 10, 26, 76, 232]
    assert ee.derangements_egf()[:9] == [1, 0, 1, 2, 9, 44, 265, 1854, 14833]


def test_brute_force_agrees_with_egfs():
    bell, inv, der = ee.set_partitions_egf(), ee.involutions_egf(), ee.derangements_egf()
    for n in range(7):
        assert ee.count_set_partitions(n) == bell[n]
        assert ee.count_involutions(n) == inv[n]
        assert ee.count_derangements(n) == der[n]


def test_series_exp_and_mul():
    # exp(x) via the recurrence equals the known series
    x = [Fraction(0), Fraction(1)] + [Fraction(0)] * (ee.N - 1)
    assert ee.series_exp(x) == ee.exp_series()
    # e^x * e^(-x) = 1
    one = ee.series_mul(ee.exp_series(), ee.exp_series(-1))
    assert one == [Fraction(1)] + [Fraction(0)] * ee.N
    with pytest.raises(ValueError):
        ee.series_exp([Fraction(1)] + [Fraction(0)] * ee.N)


def test_derangement_recurrence_and_limit():
    d = ee.derangements_egf()
    for n in range(2, ee.N + 1):
        assert d[n] == (n - 1) * (d[n - 1] + d[n - 2])
    for n in range(1, ee.N + 1):
        assert abs(d[n] / math.factorial(n) - math.exp(-1)) <= 1 / math.factorial(n + 1)
