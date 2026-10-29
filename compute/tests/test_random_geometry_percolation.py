import math
import random

import pytest

import random_geometry_percolation as rp


class BitRng:
    """A fake random source: the k-th call returns 0.25 (open) or 0.75 (closed)
    according to bit k of a mask, so all configurations can be enumerated."""

    def __init__(self, mask):
        self.mask, self.k = mask, 0

    def random(self):
        bit = (self.mask >> self.k) & 1
        self.k += 1
        return 0.25 if bit else 0.75


@pytest.mark.parametrize("n", [1, 2])
def test_self_dual_rectangle_crosses_with_probability_exactly_half(n):
    edges = (n + 1) * (n + 1) + n * n
    crossings = 0
    for mask in range(2 ** edges):
        rng = BitRng(mask)
        crossings += rp.crosses(n, 0.5, rng)
        assert rng.k == edges  # every edge sampled exactly once
    assert crossings == 2 ** (edges - 1)


def test_extreme_probabilities():
    rng = random.Random(0)
    assert rp.crossing_probability(6, 0.0, 10, rng) == 0.0
    assert rp.crossing_probability(6, 1.0, 10, rng) == 1.0


def test_union_find_components():
    parent, size = list(range(6)), [1] * 6
    rp.union(parent, size, 0, 1)
    rp.union(parent, size, 1, 2)
    rp.union(parent, size, 4, 5)
    assert rp.find(parent, 2) == rp.find(parent, 0)
    assert rp.find(parent, 3) != rp.find(parent, 0)
    assert size[rp.find(parent, 0)] == 3


def test_giant_fraction_equation():
    assert rp.giant_fraction(0.5) == 0.0
    assert rp.giant_fraction(1.0) == 0.0
    for c in [1.5, 2.0, 4.0]:
        b = rp.giant_fraction(c)
        assert 0 < b < 1
        assert b == pytest.approx(1 - math.exp(-c * b), abs=1e-12)
    assert rp.giant_fraction(2.0) == pytest.approx(0.7968121300, abs=1e-8)


def test_giant_component_simulation_matches_theory_roughly():
    rng = random.Random(42)
    assert rp.largest_component_fraction(3000, 2.0, rng) == pytest.approx(0.797, abs=0.05)
    assert rp.largest_component_fraction(3000, 0.5, rng) < 0.02


def test_crossing_sharpens_away_from_half():
    rng = random.Random(7)
    assert rp.crossing_probability(20, 0.3, 40, rng) < 0.1
    assert rp.crossing_probability(20, 0.7, 40, rng) > 0.9
