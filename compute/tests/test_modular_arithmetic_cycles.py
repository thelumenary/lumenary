import math

import pytest

import modular_arithmetic_cycles as mc


def test_power_cycles_last_digits():
    assert mc.power_cycle(2, 10) == (1, [2, 4, 8, 6])
    assert mc.power_cycle(3, 10) == (0, [1, 3, 9, 7])
    assert mc.power_cycle(7, 10) == (0, [1, 7, 9, 3])
    assert mc.power_cycle(2, 7) == (0, [1, 2, 4])
    assert mc.power_cycle(4, 12) == (1, [4])
    with pytest.raises(ValueError):
        mc.power_cycle(2, 0)


@pytest.mark.parametrize("base,n", [(2, 10), (3, 10), (7, 10), (2, 7), (6, 9), (5, 12)])
def test_remainder_from_cycle_matches_pow(base, n):
    for e in range(0, 200):
        assert mc.remainder_from_cycle(base, e, n) == pow(base, e, n)
    assert mc.remainder_from_cycle(base, 2026, n) == pow(base, 2026, n)


def test_seven_power_2026_ends_in_nine():
    assert mc.remainder_from_cycle(7, 2026, 10) == 9 == pow(7, 2026) % 10


def test_realign_is_lcm():
    for p, q in [(10, 12), (260, 365), (4, 6), (7, 5), (3, 3)]:
        assert mc.realign(p, q) == math.lcm(p, q)
    assert mc.realign(260, 365) == 18980 == 52 * 365


def test_weekday_after():
    assert mc.weekday_after("Thursday", 0) == "Thursday"
    assert mc.weekday_after("Thursday", 7) == "Thursday"
    assert mc.weekday_after("Thursday", 100) == "Saturday"
    assert mc.weekday_after("Thursday", 365) == "Friday"
    assert mc.weekday_after("Monday", -1) == "Sunday"
