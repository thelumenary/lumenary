import math

import numpy as np
import pytest

import harmonic_analysis_gibbs_fejer as hg


def test_partial_sums_converge_away_from_jump():
    x = np.array([math.pi / 2, 1.0, 2.0])
    assert np.allclose(hg.partial_sum(2001, x), 1.0, atol=2e-3)
    assert np.allclose(hg.partial_sum(2001, -x), -1.0, atol=2e-3)
    assert hg.partial_sum(0, np.array([1.0]))[0] == 0


def test_sine_integral_value():
    assert hg.sine_integral(math.pi) == pytest.approx(1.851937052, abs=1e-8)
    assert hg.sine_integral(0.0) == 0


def test_gibbs_overshoot_persists():
    grid = np.linspace(1e-6, math.pi / 2, 20001)
    gibbs = 2 / math.pi * hg.sine_integral(math.pi)
    for n in [49, 199]:
        top = float(np.max(hg.partial_sum(n, grid)))
        assert top > 1.17
        assert abs(top - gibbs) < 5e-3


def test_fejer_means_bounded_by_one():
    grid = np.linspace(-math.pi, math.pi, 4001)
    for n in [5, 50, 200]:
        assert np.max(np.abs(hg.fejer_mean(n, grid))) <= 1 + 1e-12


def test_parseval_error_decreases_to_zero():
    errs = [hg.l2_error_squared(n) for n in [1, 9, 99, 999, 9999]]
    assert all(a > b > 0 for a, b in zip(errs, errs[1:]))
    assert errs[-1] < 1e-3
    assert hg.l2_error_squared(0) == 2


def test_odd_reciprocal_squares_limit():
    assert hg.odd_reciprocal_squares(1) == 1
    assert hg.odd_reciprocal_squares(10 ** 5) == pytest.approx(math.pi ** 2 / 8, abs=1e-5)
