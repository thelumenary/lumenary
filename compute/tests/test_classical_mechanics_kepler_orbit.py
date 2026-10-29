import math

import pytest

import classical_mechanics_kepler_orbit as ko

START = (1.0, 0.0, 0.0, 1.2)


def test_kepler_predictions():
    E, L, e, a, T = ko.kepler_predictions(START)
    assert E == pytest.approx(-0.28)
    assert L == pytest.approx(1.2)
    assert e == pytest.approx(0.44)
    assert a == pytest.approx(1 / 0.56)
    assert T == pytest.approx(2 * math.pi * (1 / 0.56) ** 1.5)
    # Perihelion is the starting radius, since v is perpendicular to r there.
    assert a * (1 - e) == pytest.approx(1.0)


def test_circular_orbit_has_zero_eccentricity():
    E, L, e, a, T = ko.kepler_predictions((1.0, 0.0, 0.0, 1.0))
    assert e == pytest.approx(0.0, abs=1e-7)
    assert a == pytest.approx(1.0)
    assert T == pytest.approx(2 * math.pi)


def test_verlet_conserves_angular_momentum_and_energy():
    states = ko.run(ko.verlet_step, START, 0.002, 10000)
    L0 = ko.ang_mom(*START)
    E0 = ko.energy(*START)
    assert max(abs(ko.ang_mom(*s) - L0) for s in states) < 1e-10
    assert max(abs(ko.energy(*s) - E0) for s in states) < 1e-4


def test_euler_gains_energy():
    states = ko.run(ko.euler_step, START, 0.002, 10000)
    assert ko.energy(*states[-1]) > ko.energy(*START) + 1e-3


def test_period_and_turning_points_match_kepler():
    E, L, e, a, T = ko.kepler_predictions(START)
    states = ko.run(ko.verlet_step, START, 0.001, 20000)
    assert ko.first_return_time(states, 0.001) == pytest.approx(T, rel=1e-4)
    radii = [math.hypot(s[0], s[1]) for s in states]
    assert min(radii) == pytest.approx(a * (1 - e), rel=1e-4)
    assert max(radii) == pytest.approx(a * (1 + e), rel=1e-4)


def test_accel_is_inverse_square():
    ax, ay = ko.accel(2.0, 0.0)
    assert (ax, ay) == pytest.approx((-0.25, 0.0))
    ax, ay = ko.accel(0.0, -3.0)
    assert (ax, ay) == pytest.approx((0.0, 1 / 9))
