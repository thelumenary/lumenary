import random
from fractions import Fraction

import probability_rules_simulation as ps


def first_even(t):
    return t[0] % 2 == 0


def total_seven(t):
    return t[0] + t[1] == 7


def test_exact_values():
    assert ps.exact(first_even) == Fraction(1, 2)
    assert ps.exact(first_even, total_seven) == Fraction(1, 2)
    assert ps.exact(lambda t: t[0] == 6, lambda t: t[0] + t[1] >= 10) == \
        Fraction(1, 2)
    assert ps.exact(lambda t: t[0] == 1, lambda t: t[0] == 6) == 0


def test_estimate_on_hand_made_trials():
    trials = [(1, 6), (2, 5), (4, 3), (6, 6)]
    assert ps.estimate(trials, first_even) == 0.75
    assert ps.estimate(trials, first_even, total_seven) == 2 / 3


def test_rolls_are_faces_and_frequencies_settle():
    rolls = ps.roll_pairs(random.Random(3), 40000)
    assert all(1 <= a <= 6 and 1 <= b <= 6 for a, b in rolls)
    assert abs(ps.estimate(rolls, first_even, total_seven) - 0.5) < 0.03


def test_monty_hall_rates():
    stick, switch = ps.monty_hall(random.Random(5), 20000)
    assert abs(stick + switch - 1) < 1e-12  # exactly one of the two wins
    assert abs(switch - 2 / 3) < 0.02


def test_second_ace():
    est = ps.second_ace_given_first(random.Random(9), 60000)
    assert abs(est - 3 / 51) < 0.015
