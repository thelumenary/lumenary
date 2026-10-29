import math

import pytest

import mathematical_biology_lotka_volterra as ex


def test_equilibrium_is_stationary():
    fx, fy = ex.rhs(ex.C / ex.D, ex.A / ex.B)
    assert fx == pytest.approx(0.0) and fy == pytest.approx(0.0)


def test_conserved_quantity_has_zero_derivative():
    x, y = 4.0, 1.0
    fx, fy = ex.rhs(x, y)
    dv = (ex.D - ex.C / x) * fx + (ex.B - ex.A / y) * fy
    assert dv == pytest.approx(0.0, abs=1e-12)


def test_euler_drifts_rk4_conserves():
    eul = ex.run(ex.euler_step, 4.0, 1.0, 0.01, 2000)
    rk = ex.run(ex.rk4_step, 4.0, 1.0, 0.01, 2000)
    v0 = ex.conserved(4.0, 1.0)
    assert ex.conserved(*eul[-1]) - v0 > 0.01
    assert abs(ex.conserved(*rk[-1]) - v0) < 1e-6


def test_euler_drift_increases_monotonically():
    eul = ex.run(ex.euler_step, 4.0, 1.0, 0.01, 1000)
    values = [ex.conserved(*p) for p in eul[::100]]
    assert values == sorted(values)


def test_cycle_averages_equal_equilibrium():
    period, ax, ay = ex.period_and_averages(4.0, 1.0)
    assert ax == pytest.approx(ex.C / ex.D, abs=2e-3)
    assert ay == pytest.approx(ex.A / ex.B, abs=2e-3)
    assert period > 2 * math.pi / math.sqrt(ex.A * ex.C)
