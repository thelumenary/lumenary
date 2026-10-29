from fractions import Fraction

import pytest

import rational_numbers_decimals as rd


def test_long_division_known_expansions():
    assert rd.long_division(1, 7) == (0, [1, 4, 2, 8, 5, 7], 0, 6)
    assert rd.long_division(1, 6) == (0, [1, 6], 1, 1)
    assert rd.long_division(3, 8) == (0, [3, 7, 5, 0], 3, 1)
    assert rd.long_division(22, 7)[0] == 3


def test_long_division_rejects_bad_input():
    with pytest.raises(ValueError):
        rd.long_division(1, 0)
    with pytest.raises(ValueError):
        rd.long_division(-1, 3)


def test_decimal_strings():
    assert rd.decimal_string(1, 3) == "0.(3)"
    assert rd.decimal_string(5, 12) == "0.41(6)"
    assert rd.decimal_string(3, 8) == "0.375"
    assert rd.decimal_string(6, 3) == "2"
    assert rd.decimal_string(3, 11) == "0.(27)"


def test_only_twos_and_fives():
    assert [n for n in range(1, 30) if rd.only_twos_and_fives(n)] == [
        1, 2, 4, 5, 8, 10, 16, 20, 25]


def test_to_fraction_round_trips():
    assert rd.to_fraction(0, "", "27") == Fraction(3, 11)
    assert rd.to_fraction(0, "1", "6") == Fraction(1, 6)
    assert rd.to_fraction(0, "", "9") == 1
    assert rd.to_fraction(2, "375", "") == Fraction(19, 8)
    for a, b in [(1, 7), (5, 12), (13, 28), (100, 101)]:
        whole, digits, start, _ = rd.long_division(a, b)
        pre = "".join(map(str, digits[:start]))
        block = "".join(map(str, digits[start:]))
        assert rd.to_fraction(whole, pre, block) == Fraction(a, b)


def test_period_bound_and_rule_hold_up_to_60():
    cases, bad_period, bad_rule, bad_trip = rd.check_all(60)
    assert cases == 60 * 61 // 2
    assert (bad_period, bad_rule, bad_trip) == (0, 0, 0)


def test_full_period_primes():
    # 1/p has the longest possible period p - 1 for these primes.
    for p in [7, 17, 19, 23, 29]:
        assert rd.long_division(1, p)[3] == p - 1
