from fractions import Fraction
from math import gcd

import pytest

import fractions_decimal_expansions as fde


def test_terminating_expansions():
    assert fde.decimal_expansion(1, 8) == (0, [1, 2, 5], [])
    assert fde.decimal_expansion(37, 100) == (0, [3, 7], [])
    assert fde.decimal_expansion(5, 4) == (1, [2, 5], [])
    assert fde.show(3, 12) == "0.25"
    assert fde.show(6, 3) == "2"


def test_repeating_expansions():
    assert fde.decimal_expansion(1, 3) == (0, [], [3])
    assert fde.decimal_expansion(1, 6) == (0, [1], [6])
    assert fde.decimal_expansion(1, 7) == (0, [], [1, 4, 2, 8, 5, 7])
    assert fde.show(1, 12) == "0.08(3)"
    assert fde.show(22, 7) == "3.(142857)"


def test_expansion_reconstructs_the_fraction():
    for b in range(1, 40):
        for a in range(0, 2 * b):
            whole, fixed, repeat = fde.decimal_expansion(a, b)
            k, p = len(fixed), len(repeat)
            value = Fraction(whole) + Fraction(int("".join(map(str, fixed)) or "0"), 10 ** k)
            if p:
                block = int("".join(map(str, repeat)))
                value += Fraction(block, 10 ** k * (10 ** p - 1))
            assert value == Fraction(a, b), (a, b)


def test_only_twos_and_fives():
    assert [n for n in range(1, 30) if fde.only_twos_and_fives(n)] == [1, 2, 4, 5, 8, 10, 16, 20, 25]
    with pytest.raises(ValueError):
        fde.only_twos_and_fives(0)
    with pytest.raises(ValueError):
        fde.decimal_expansion(1, 0)


def test_rule_holds_for_small_denominators():
    checked, correct, stops = fde.check_rule(30)
    assert checked == correct == sum(range(1, 30))
    expected = sum(
        1 for b in range(2, 31) for a in range(1, b) if fde.only_twos_and_fives(b // gcd(a, b))
    )
    assert stops == expected
