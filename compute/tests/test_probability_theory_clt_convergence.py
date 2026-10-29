import math

import numpy as np
import pytest

import probability_theory_clt_convergence as ex

DIE = [0] + [1 / 6] * 6
COIN = [0.9, 0.1]


def test_sum_distribution_two_dice():
    probs = ex.sum_distribution(DIE, 2)
    assert len(probs) == 13
    assert probs[7] == pytest.approx(6 / 36)
    assert probs[2] == pytest.approx(1 / 36)
    assert probs.sum() == pytest.approx(1.0)


def test_sum_distribution_is_binomial_for_coin():
    probs = ex.sum_distribution(COIN, 10)
    for k in range(11):
        assert probs[k] == pytest.approx(math.comb(10, k) * 0.1 ** k * 0.9 ** (10 - k))
    with pytest.raises(ValueError):
        ex.sum_distribution(COIN, 0)


def test_moments():
    mu, sigma, rho = ex.moments(DIE)
    assert mu == pytest.approx(3.5)
    assert sigma ** 2 == pytest.approx(35 / 12)
    assert rho == pytest.approx(6.375)
    mu, sigma, rho = ex.moments(COIN)
    assert (mu, sigma ** 2) == pytest.approx((0.1, 0.09))
    assert rho == pytest.approx(0.09 * 0.82)


def test_phi():
    assert ex.phi(0) == pytest.approx(0.5)
    assert ex.phi(1.96) == pytest.approx(0.975, abs=1e-3)
    assert ex.phi(-1) + ex.phi(1) == pytest.approx(1.0)


def test_single_coin_distance():
    # One coin flip, standardised: jumps at z = -1/3 (to 0.9) and z = 3.
    d = ex.kolmogorov_distance(COIN, 1)
    expected = max(abs(ex.phi(-1 / 3) - 0.9), ex.phi(-1 / 3), 1 - ex.phi(3))
    assert d == pytest.approx(expected)


@pytest.mark.parametrize("n", [1, 4, 16, 64, 256])
@pytest.mark.parametrize("pmf", [DIE, COIN])
def test_berry_esseen_holds(pmf, n):
    assert ex.kolmogorov_distance(pmf, n) <= ex.berry_esseen_bound(pmf, n)


def test_distance_decreases():
    ds = [ex.kolmogorov_distance(DIE, n) for n in [1, 4, 16, 64]]
    assert all(a > b for a, b in zip(ds, ds[1:]))
