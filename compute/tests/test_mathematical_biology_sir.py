import math

import pytest

import mathematical_biology_sir as ex


def test_rhs_conserves_total():
    ds, di, dr = ex.sir_rhs((0.7, 0.2, 0.1), 0.3, 0.1)
    assert ds + di + dr == pytest.approx(0.0)
    assert ds < 0


def test_rk4_step_conserves_total():
    state = (0.9, 0.1, 0.0)
    for _ in range(100):
        state = ex.rk4_step(state, 0.5, 0.3, 0.1)
    assert sum(state) == pytest.approx(1.0, abs=1e-12)


def test_final_size_relation():
    for r0 in [1.5, 2.0, 3.0, 5.0]:
        s = ex.final_size(r0)
        assert 0 < s < 1 / r0
        assert s == pytest.approx(math.exp(-r0 * (1 - s)), abs=1e-14)
    assert 1 - ex.final_size(2.0) == pytest.approx(0.7968, abs=1e-4)


def test_peak_formula():
    assert ex.peak_prevalence(3.0) == pytest.approx(1 - (1 + math.log(3)) / 3)
    assert ex.peak_prevalence(1.0) == pytest.approx(0.0)


def test_simulation_matches_theory():
    s_end, peak, day, drift = ex.simulate(3.0)
    assert 1 - s_end == pytest.approx(1 - ex.final_size(3.0), abs=2e-3)
    assert peak == pytest.approx(ex.peak_prevalence(3.0), abs=2e-3)
    assert drift < 1e-6
    assert 1 - s_end > 1 - 1 / 3  # overshoot beyond the herd immunity threshold


def test_subcritical_epidemic_dies_out():
    s_end, peak, _, _ = ex.simulate(0.8)
    assert peak <= 1e-4 + 1e-12
    assert 1 - s_end < 1e-3
