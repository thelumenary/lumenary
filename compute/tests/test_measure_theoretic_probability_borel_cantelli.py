import math
import random
from fractions import Fraction

import pytest

import measure_theoretic_probability_borel_cantelli as bc


def test_block_expectations_exact_small_cases():
    assert bc.block_expectation(0, 1) == 1
    assert bc.block_expectation(1, 1) == Fraction(1, 2) + Fraction(1, 3)
    assert bc.block_expectation(1, 2) == Fraction(1, 4) + Fraction(1, 9)
    with pytest.raises(ValueError):
        bc.block_expectation(-1, 1)
    with pytest.raises(ValueError):
        bc.block_expectation(2, 0)


def test_harmonic_blocks_decrease_to_ln2():
    vals = [bc.block_expectation(k, 1) for k in range(9)]
    assert all(a > b for a, b in zip(vals, vals[1:]))
    # integral comparison: ln 2 < block sum <= ln 2 + 1/2^(k+1)
    for k, v in enumerate(vals):
        assert math.log(2) < float(v) <= math.log(2) + 2.0 ** -(k + 1) + 1e-12


def test_square_blocks_are_summable():
    # block k of 1/n^2 is at most 2^k * 4^-k = 2^-k, so the series converges
    for k in range(9):
        assert bc.block_expectation(k, 2) <= Fraction(1, 2 ** k)


def test_block_counts_and_simulation():
    assert bc.block_counts([1, 2, 3, 4, 7, 8, 1000], 3) == [1, 2, 2, 1]
    hits = bc.simulate(1, 100, random.Random(0))
    assert hits[0] == 1  # P(A_1) = 1
    assert all(1 <= n <= 100 for n in hits)
    assert hits == sorted(set(hits))


def test_simulation_is_seeded_and_matches_expectation_roughly():
    rng = random.Random(5)
    totals = [len(bc.simulate(1, 2 ** 10 - 1, rng)) for _ in range(200)]
    mean = sum(totals) / len(totals)
    harmonic = sum(1 / n for n in range(1, 2 ** 10))
    assert abs(mean - harmonic) < 0.5
    assert bc.simulate(2, 50, random.Random(3)) == bc.simulate(2, 50, random.Random(3))
