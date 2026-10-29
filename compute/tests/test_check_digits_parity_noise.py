import itertools
import math

import pytest

import check_digits_parity_noise as pn


def test_with_parity_makes_even_words():
    for data in itertools.product([0, 1], repeat=7):
        word = pn.with_parity(data)
        assert len(word) == 8 and pn.accepted(word)


def test_single_flip_rejected_double_flip_accepted():
    word = pn.with_parity([1, 0, 1, 1, 0, 0, 1])
    for i in range(8):
        one = list(word)
        one[i] ^= 1
        assert not pn.accepted(one)
        for j in range(i + 1, 8):
            two = list(one)
            two[j] ^= 1
            assert pn.accepted(two)


@pytest.mark.parametrize("p", [0.0, 0.01, 0.2, 0.5, 1.0])
def test_exact_probabilities_sum_to_one(p):
    intact, rejected, undetected = pn.exact_probabilities(p)
    assert math.isclose(intact + rejected + undetected, 1.0)
    # Closed forms: odd number of flips has probability (1 - (1 - 2p)^n) / 2.
    assert math.isclose(rejected, (1 - (1 - 2 * p) ** 8) / 2, abs_tol=1e-12)
    assert math.isclose(intact, (1 - p) ** 8, abs_tol=1e-12)


def test_simulation_is_deterministic_and_close_to_exact():
    a = pn.simulate(0.05, 4000, seed=1)
    assert a == pn.simulate(0.05, 4000, seed=1)
    assert sum(a) == 4000
    exp = [4000 * q for q in pn.exact_probabilities(0.05)]
    for got, want in zip(a, exp):
        # within 5 standard deviations of a binomial count
        sd = math.sqrt(4000 * (want / 4000) * (1 - want / 4000))
        assert abs(got - want) <= 5 * sd + 1


def test_no_noise_means_everything_intact():
    assert pn.simulate(0.0, 500, seed=3) == (500, 0, 0)
    assert pn.exact_probabilities(0.0) == (1.0, 0.0, 0.0)
