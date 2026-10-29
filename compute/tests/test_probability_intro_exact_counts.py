from fractions import Fraction

import probability_intro_exact_counts as pe


def test_two_dice_sums_are_triangular():
    counts = pe.sum_counts(2)
    assert sum(counts.values()) == 36
    assert [counts[s] for s in range(2, 13)] == [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1]


def test_galileo_three_dice():
    counts = pe.sum_counts(3)
    assert sum(counts.values()) == 216
    assert (counts[9], counts[10]) == (25, 27)
    assert len(pe.partitions(9)) == len(pe.partitions(10)) == 6
    assert (1, 2, 6) in pe.partitions(9) and (3, 3, 3) in pe.partitions(9)
    # Symmetry: sum s and sum 21 - s are equally likely.
    assert all(counts[s] == counts[21 - s] for s in range(3, 19))


def test_probability_helper():
    assert pe.probability(lambda o: o % 2 == 0, range(1, 7)) == Fraction(1, 2)
    assert pe.probability(lambda o: o > 6, range(1, 7)) == 0


def test_dalembert():
    coins = ["HH", "HT", "TH", "TT"]
    assert pe.probability(lambda c: "H" in c, coins) == Fraction(3, 4)


def test_de_mere_bets():
    assert pe.at_least_one_six(4) == Fraction(671, 1296)
    assert pe.at_least_one_six(1) == Fraction(1, 6)
    assert pe.at_least_one_six(3) == 1 - Fraction(5, 6) ** 3
    p24 = pe.at_least_one_double_six(24)
    assert Fraction(49, 100) < p24 < Fraction(1, 2)
    # 25 throws tip the bet over one half.
    assert pe.at_least_one_double_six(25) > Fraction(1, 2)
