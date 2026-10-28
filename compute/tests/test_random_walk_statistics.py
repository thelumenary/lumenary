from fractions import Fraction
from math import comb
import random

import pytest

import random_walk_statistics as rw


def test_first_return_time_is_even_or_none():
    rng = random.Random(1)
    for _ in range(500):
        t = rw.first_return_time(rng, 50)
        assert t is None or (t % 2 == 0 and 2 <= t <= 50)


def test_first_return_time_zero_steps():
    assert rw.first_return_time(random.Random(0), 0) is None


def test_simulate_is_reproducible_and_seed_dependent():
    assert rw.simulate(200, 100, seed=5) == rw.simulate(200, 100, seed=5)
    assert rw.simulate(200, 100, seed=5) != rw.simulate(200, 100, seed=6)
    assert len(rw.simulate(37, 10, seed=1)) == 37


def test_returned_within():
    times = [2, 4, None, 10, 2]
    assert rw.returned_within(times, 1) == 0
    assert rw.returned_within(times, 2) == 2
    assert rw.returned_within(times, 4) == 3
    assert rw.returned_within(times, 100) == 4


@pytest.mark.parametrize("h,expected", [(0, Fraction(0)), (1, Fraction(0)), (2, Fraction(1, 2)), (3, Fraction(1, 2)), (4, Fraction(5, 8)), (6, Fraction(11, 16))])
def test_exact_return_probability_small(h, expected):
    assert rw.exact_return_probability(h) == expected


def test_exact_return_probability_by_brute_force():
    # Enumerate all 2^h coin-flip sequences for small h.
    from itertools import product
    for h in range(0, 13):
        hits = 0
        for steps in product((1, -1), repeat=h):
            pos = 0
            for s in steps:
                pos += s
                if pos == 0:
                    hits += 1
                    break
        assert rw.exact_return_probability(h) == Fraction(hits, 2 ** h)


def test_exact_return_probability_increases_towards_one():
    values = [rw.exact_return_probability(h) for h in range(0, 2001, 100)]
    assert all(a <= b for a, b in zip(values, values[1:]))
    assert values[-1] < 1
    assert rw.exact_return_probability(1000) == 1 - Fraction(comb(1000, 500), 4 ** 500)


def test_exact_return_probability_rejects_negative():
    with pytest.raises(ValueError):
        rw.exact_return_probability(-2)


def test_wilson_interval_properties():
    low, high = rw.wilson_interval(50, 100)
    assert low < 0.5 < high
    assert abs((low + high) / 2 - 0.5) < 1e-12
    low0, high0 = rw.wilson_interval(0, 10)
    assert low0 == 0.0 and 0 < high0 < 0.35
    low1, high1 = rw.wilson_interval(10, 10)
    assert high1 == 1.0 and 0.65 < low1 < 1
    narrow = rw.wilson_interval(5000, 10000)
    assert narrow[1] - narrow[0] < high - low


@pytest.mark.parametrize("successes,trials", [(1, 0), (-1, 10), (11, 10)])
def test_wilson_interval_rejects_bad_input(successes, trials):
    with pytest.raises(ValueError):
        rw.wilson_interval(successes, trials)


def test_main_seed_estimates_are_consistent_with_exact_values():
    times = rw.simulate(4000, max(rw.HORIZONS), rw.SEED)
    for h in rw.HORIZONS:
        low, high = rw.wilson_interval(rw.returned_within(times, h), 4000)
        assert low <= float(rw.exact_return_probability(h)) <= high
