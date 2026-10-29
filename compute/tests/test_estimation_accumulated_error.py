import random

import pytest

import estimation_accumulated_error as eae


def test_round_ten_values():
    assert [eae.round_ten(n) for n in (0, 4, 5, 14, 15, 37, 999)] == [0, 0, 10, 10, 20, 40, 1000]
    with pytest.raises(ValueError):
        eae.round_ten(-1)


def test_single_rounding_error_is_between_minus_4_and_5():
    errors = {eae.round_ten(n) - n for n in range(1000)}
    assert errors == set(range(-4, 6))


def test_round_first_error_examples():
    assert eae.round_first_error([14, 14, 14]) == 30 - 42
    assert eae.round_first_error([15, 15, 15]) == 60 - 45
    assert eae.round_first_error([]) == 0


def test_exhaustive_triples_small():
    count, low, high, differ = eae.exhaustive_triples(20)
    assert count == 20 ** 3
    assert (low, high) == (-12, 15)
    assert 0 < differ < count


def test_simulated_errors_respect_the_bound():
    rng = random.Random(1)
    for k in (1, 5, 20):
        errors = eae.simulate(k, 300, rng)
        assert len(errors) == 300
        assert all(-4 * k <= e <= 5 * k for e in errors)
