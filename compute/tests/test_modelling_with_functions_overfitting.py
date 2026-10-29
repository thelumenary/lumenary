import math

import modelling_with_functions_overfitting as mo


def test_true_curve():
    assert mo.true_temperature(0) == 85
    assert 25 <= mo.true_temperature(100) < 25.01  # approaches room temperature
    assert math.isclose(mo.true_temperature(10), 25 + 60 / math.e)


def test_readings_are_seeded_and_close_to_truth():
    ts, temps = mo.synthetic_readings()
    assert ts == [0, 2, 4, 6, 8, 10, 12, 14]
    assert (ts, temps) == mo.synthetic_readings()
    assert all(abs(T - mo.true_temperature(t)) < 2 for t, T in zip(ts, temps))


def test_lagrange_interpolates_exactly():
    xs, ys = [0, 1, 2, 4], [1.0, -2.0, 0.5, 3.0]
    for x, y in zip(xs, ys):
        assert math.isclose(mo.lagrange(xs, ys, x), y)
    # through points of a cubic it reproduces the cubic everywhere
    cubic = lambda x: x ** 3 - 2 * x + 1  # noqa: E731
    xs = [-1, 0, 1, 2]
    assert math.isclose(mo.lagrange(xs, [cubic(x) for x in xs], 3.5), cubic(3.5))


def test_newton_fit_recovers_noise_free_parameters():
    ts = [0, 2, 4, 6]
    temps = [mo.true_temperature(t) for t in ts]
    d, k = mo.fit_newton(ts, temps)
    assert math.isclose(d, 60) and math.isclose(k, 0.1)


def test_overfit_polynomial_extrapolates_badly():
    ts, temps = mo.synthetic_readings()
    assert mo.rms([mo.lagrange(ts, temps, t) - T for t, T in zip(ts, temps)]) < 1e-9
    assert abs(mo.lagrange(ts, temps, 30) - mo.true_temperature(30)) > 100
    d, k = mo.fit_newton(ts, temps)
    assert abs(25 + d * math.exp(-k * 30) - mo.true_temperature(30)) < 1
