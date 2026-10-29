import math

import numpy as np

import statistical_inference_intro_sampling as ss


def test_true_proportion():
    assert ss.P_TRUE == 0.38


def test_standard_error_formula():
    se = ss.standard_error(0.38, 100)
    assert abs(se - math.sqrt(0.38 * 0.62 / 100) *
               math.sqrt((20000 - 100) / 19999)) < 1e-12
    # quadrupling n roughly halves the standard error (exactly without fpc)
    ratio = ss.standard_error(0.38, 400, 10**12) / \
        ss.standard_error(0.38, 1600, 10**12)
    assert abs(ratio - 2) < 1e-6
    # sampling the whole population leaves no variability
    assert ss.standard_error(0.38, 20000) == 0


def test_srs_estimates_are_unbiased_and_spread_as_predicted():
    rng = np.random.default_rng(7)
    est = ss.srs_estimates(rng, 100, 20000)
    assert np.all((0 <= est) & (est <= 1))
    assert abs(est.mean() - 0.38) < 0.003
    assert abs(est.std() - ss.standard_error(0.38, 100)) < 0.002


def test_coverage_near_95_percent():
    rng = np.random.default_rng(11)
    est = ss.srs_estimates(rng, 400, 20000)
    assert abs(ss.coverage(est, 400) - 0.95) < 0.01
    assert ss.coverage(np.array([0.38, 0.9]), 400) == 0.5


def test_voluntary_response_is_biased():
    rng = np.random.default_rng(13)
    expected = 0.38 * 0.6 / (0.38 * 0.6 + 0.62 * 0.2)
    est = ss.voluntary_response(rng, 100000, 0.6, 0.2)
    assert abs(est - expected) < 0.01
    # equal reply rates remove the bias
    fair = ss.voluntary_response(rng, 100000, 0.3, 0.3)
    assert abs(fair - 0.38) < 0.01
