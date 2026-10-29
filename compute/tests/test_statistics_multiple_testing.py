import random

import pytest

import statistics_multiple_testing as ex


def test_p_value():
    assert ex.p_value(0) == pytest.approx(1.0)
    assert ex.p_value(1.959964) == pytest.approx(0.05, abs=1e-6)
    assert ex.p_value(-2.0) == ex.p_value(2.0)


def test_bonferroni():
    ps = [0.001, 0.01, 0.02, 0.2]
    assert ex.bonferroni(ps, 0.05) == {0, 1}  # threshold 0.0125
    assert ex.bonferroni([0.5], 0.05) == set()


def test_benjamini_hochberg_step_up():
    ps = [0.001, 0.008, 0.039, 0.041, 0.042, 0.06, 0.074, 0.205, 0.212, 0.216]
    # Thresholds k * 0.05 / 10 = 0.005, 0.010, 0.015, ...; only the first two pass.
    assert ex.benjamini_hochberg(ps, 0.05) == {0, 1}
    # Step-up: a later p-value under its threshold rescues earlier ones.
    assert ex.benjamini_hochberg([0.04, 0.04], 0.05) == {0, 1}
    assert ex.benjamini_hochberg([0.9, 0.8], 0.05) == set()


def test_bh_rejects_at_least_what_bonferroni_rejects():
    rng = random.Random(3)
    for _ in range(200):
        ps = ex.simulate(rng, 30, 5)
        assert ex.bonferroni(ps, 0.05) <= ex.benjamini_hochberg(ps, 0.05)


def test_simulate_shapes_and_effects():
    rng = random.Random(0)
    ps = ex.simulate(rng, 50, 10)
    assert len(ps) == 50
    assert all(0 <= p <= 1 for p in ps)
    rng = random.Random(1)
    strong = [ex.simulate(rng, 2, 1, shift=8.0) for _ in range(50)]
    assert all(row[0] < 1e-6 for row in strong)
