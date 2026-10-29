import math

import pytest

import relativity_geodesics as rg


def test_rk4_step_on_harmonic_oscillator():
    def f(_phi, y):
        return [y[1], -y[0]]
    y, h = [0.0, 1.0], 0.01
    phi = 0.0
    for _ in range(314):
        y = rg.rk4_step(f, phi, y, h)
        phi += h
    assert y[0] == pytest.approx(math.sin(3.14), abs=1e-9)


def test_flat_space_has_no_bending_or_precession():
    assert rg.light_deflection(0.0, 10.0) == pytest.approx(0.0, abs=1e-9)
    assert rg.perihelion_advance(1e-12, 50.0, 0.3) == pytest.approx(0.0, abs=1e-8)


def test_weak_field_limits():
    b = 2000.0
    d = rg.light_deflection(1.0, b)
    assert d == pytest.approx(4 / b + 15 * math.pi / (4 * b * b), rel=1e-4)
    p = 5000.0
    assert rg.perihelion_advance(1.0, p, 0.2) == pytest.approx(6 * math.pi / p, rel=2e-3)


def test_deflection_decreases_with_impact_parameter():
    vals = [rg.light_deflection(1.0, b) for b in [8.0, 20.0, 50.0]]
    assert vals[0] > vals[1] > vals[2] > 0
