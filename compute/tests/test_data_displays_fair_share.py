import random
from fractions import Fraction

import pytest

import data_displays_fair_share as fs


def test_level_once_keeps_total_and_count():
    towers = [4, 6, 8, 2]
    nxt = fs.level_once(towers)
    assert sum(nxt) == sum(towers) and len(nxt) == len(towers)
    assert towers == [4, 6, 8, 2]  # the original is not changed
    assert fs.level_once([5, 5, 5]) is None
    assert fs.level_once([4, 5, 4]) is None


def test_level_reaches_the_mean_when_divisible():
    stages = fs.level([4, 6, 8, 2])
    assert stages[-1] == [5, 5, 5, 5]
    assert len(stages) - 1 == 4
    assert fs.mean([4, 6, 8, 2]) == 5


def test_level_when_not_divisible_ends_within_one():
    final = fs.level([3, 7, 2, 6])[-1]
    assert sum(final) == 18
    assert max(final) - min(final) == 1
    assert fs.mean([3, 7, 2, 6]) == Fraction(9, 2)


def test_random_towers_always_level_at_total_over_count():
    rng = random.Random(42)
    for _ in range(200):
        n = rng.randint(1, 8)
        towers = [rng.randint(0, 12) for _ in range(n)]
        final = fs.level(towers)[-1]
        assert sum(final) == sum(towers)
        assert max(final) - min(final) <= 1
        if sum(towers) % n == 0:
            assert final == [sum(towers) // n] * n
        assert min(towers) <= fs.mean(towers) <= max(towers)


def test_mean_of_fractions_and_errors():
    beans = [Fraction(9, 4), Fraction(5, 2), Fraction(5, 2), Fraction(11, 4),
             Fraction(13, 4), Fraction(7, 2), Fraction(7, 2), Fraction(15, 4)]
    assert fs.mean(beans) == 3
    assert fs.mean(beans) * len(beans) == sum(beans)
    assert fs.mean(beans) not in beans
    with pytest.raises(ValueError):
        fs.mean([])
