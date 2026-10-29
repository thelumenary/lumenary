import math
import random

import probability_intro_simulation as ps


def test_exact_distribution():
    assert abs(sum(ps.EXACT.values()) - 1) < 1e-12
    assert ps.EXACT[7] == 6 / 36 and ps.EXACT[2] == ps.EXACT[12] == 1 / 36


def test_roll_two_dice_counts_and_range():
    counts = ps.roll_two_dice(random.Random(1), 5000)
    assert sum(counts.values()) == 5000
    assert set(counts) <= set(range(2, 13))


def test_frequencies_settle_near_probabilities():
    rng = random.Random(7)
    n = 40000
    err = ps.largest_error(ps.roll_two_dice(rng, n), n)
    # Several standard errors of slack: fails with tiny probability only.
    assert err < 5 / math.sqrt(n)


def test_largest_error_of_perfect_counts_is_zero():
    perfect = {s: round(ps.EXACT[s] * 36) for s in range(2, 13)}
    assert ps.largest_error(perfect, 36) < 1e-12


def test_heads_after_tails():
    flips = list("TTTHTTTTHH")
    frac, cases = ps.heads_after_tails(flips, 3)
    # Positions after TTT: index 3 (H), 7 (T), 8 (H).
    assert cases == 3 and abs(frac - 2 / 3) < 1e-12
    assert ps.heads_after_tails(list("HHHH"), 3) == (None, 0)


def test_exactly_one_six_rate_close_to_exact():
    rate = ps.exactly_one_six_rate(random.Random(11), 20000)
    assert abs(rate - (5 / 6) ** 5) < 0.02
