import math

import pytest

import classical_mechanics_pendulum_period as pp


def test_agm_basic_values():
    assert pp.agm(1.0, 1.0) == 1.0
    assert pp.agm(1.0, 2.0) == pytest.approx(pp.agm(2.0, 1.0))
    # Gauss's constant: 1 / AGM(1, sqrt 2) = 0.8346268...
    assert 1 / pp.agm(1.0, math.sqrt(2)) == pytest.approx(0.8346268416740731)
    with pytest.raises(ValueError):
        pp.agm(0.0, 1.0)


def test_small_amplitude_limit_is_two_pi():
    assert pp.exact_period(0.0) == pytest.approx(2 * math.pi)
    assert pp.exact_period(1e-4) == pytest.approx(2 * math.pi, rel=1e-8)


def test_period_scales_with_omega():
    assert pp.exact_period(1.0, omega0=2.0) == pytest.approx(pp.exact_period(1.0) / 2)


def test_period_increases_with_amplitude_and_diverges():
    periods = [pp.exact_period(math.radians(d)) for d in range(0, 180, 10)]
    assert all(a < b for a, b in zip(periods, periods[1:]))
    assert pp.exact_period(math.pi - 1e-6) > 30
    with pytest.raises(ValueError):
        pp.exact_period(math.pi)


def test_series_agrees_for_small_amplitudes():
    for degrees in [1, 5, 10, 20]:
        t = math.radians(degrees)
        assert pp.series_period(t) == pytest.approx(pp.exact_period(t), rel=1e-5)


def test_simulation_matches_exact_formula():
    for degrees in [10, 90, 160]:
        t = math.radians(degrees)
        assert pp.simulated_period(t) == pytest.approx(pp.exact_period(t), rel=1e-5)
