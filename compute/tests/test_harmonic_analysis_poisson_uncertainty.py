import math

import numpy as np
import pytest

import harmonic_analysis_poisson_uncertainty as hp


def test_theta_functional_equation():
    for t in [0.05, 0.3, 1.0, 3.0, 10.0]:
        assert hp.theta(t) == pytest.approx(hp.theta(1 / t) / math.sqrt(t), rel=1e-13)


def test_theta_values():
    assert hp.theta(1.0) == pytest.approx(math.pi ** 0.25 / math.gamma(0.75), rel=1e-13)
    assert hp.theta(50.0) == pytest.approx(1.0, abs=1e-60)
    with pytest.raises(ValueError):
        hp.theta(0)


def test_trapezoid_exact_for_linear_and_gaussian():
    grid = np.linspace(0, 1, 11)
    assert hp.trapezoid(2 * grid + 1, grid) == pytest.approx(2.0)
    big = np.linspace(-10, 10, 2001)
    assert hp.trapezoid(np.exp(-math.pi * big ** 2), big) == pytest.approx(1.0)


def test_uncertainty_ratios_match_exact_values():
    exact = {"Gaussian exp(-pi x^2)": 1.0, "exp(-|x|)": 2.0, "tent max(1 - |x|, 0)": 1.2}
    for name, (f, fhat) in hp.EXAMPLES.items():
        r = hp.uncertainty_ratio(f, fhat)
        assert r >= 1 - 1e-6
        assert r == pytest.approx(exact[name], rel=2e-3)


def test_fourier_pairs_agree_at_zero():
    # fhat(0) = integral of f
    grid = np.linspace(-60, 60, 600001)
    for f, fhat in hp.EXAMPLES.values():
        assert hp.trapezoid(f(grid), grid) == pytest.approx(float(fhat(np.array([0.0]))[0]), rel=1e-6)
