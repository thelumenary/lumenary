import math
from fractions import Fraction

import pytest

import combinatorics_inclusion_exclusion as ci


@pytest.mark.parametrize("n", [1, 7, 30, 100, 997])
def test_inclusion_exclusion_matches_direct(n):
    for divisors in [(2,), (2, 3), (2, 3, 5), (4, 6), (2, 3, 5, 7)]:
        assert ci.divisible_count_ie(n, divisors) == \
            ci.divisible_count_direct(n, divisors)


def test_divisible_known_value():
    assert ci.divisible_count_ie(100, (2, 3, 5)) == 74


def test_derangements_small_values():
    assert [ci.derangements_brute(n) for n in range(7)] == \
        [1, 0, 1, 2, 9, 44, 265]
    assert [ci.derangements_ie(n) for n in range(9)] == \
        [1, 0, 1, 2, 9, 44, 265, 1854, 14833]


def test_derangement_recurrence_and_limit():
    d = [ci.derangements_ie(n) for n in range(15)]
    for n in range(2, 15):
        assert d[n] == (n - 1) * (d[n - 1] + d[n - 2])
    assert abs(d[14] / math.factorial(14) - 1 / math.e) < 1e-10


def test_birthday_probabilities():
    assert ci.shared_birthday(1) == 0
    assert ci.shared_birthday(2) == Fraction(1, 365)
    assert ci.shared_birthday(22) < Fraction(1, 2) < ci.shared_birthday(23)
    assert ci.shared_birthday(365) < 1
    assert ci.shared_birthday(366) == 1
    assert ci.shared_birthday(3, days=2) == 1
