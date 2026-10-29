import math
from fractions import Fraction

import pytest

import symplectic_geometry_integrators as si


def test_energy_values():
    assert si.energy(0.0, 0.0) == -1.0
    assert si.energy(math.pi, 0.0) == pytest.approx(1.0)
    assert si.energy(0.0, 2.0) == pytest.approx(1.0)
    assert si.force(math.pi / 2) == pytest.approx(-1.0)


@pytest.mark.parametrize("name", ["symplectic Euler", "leapfrog"])
def test_symplectic_steps_preserve_area_exactly(name):
    for h in [Fraction(1, 10), Fraction(1, 3), Fraction(7, 5)]:
        assert si.det2(si.oscillator_step_matrix(name, h)) == 1


def test_non_symplectic_steps_change_area():
    h = Fraction(1, 10)
    assert si.det2(si.oscillator_step_matrix("explicit Euler", h)) == 1 + h * h
    d = si.det2(si.oscillator_step_matrix("RK4", h))
    # |R(ih)|^2 = 1 - h^6/72 + h^8/576 for the RK4 stability polynomial
    assert d == 1 - h ** 6 / 72 + h ** 8 / 576
    assert d < 1
    with pytest.raises(ValueError):
        si.oscillator_step_matrix("midpoint", h)


def test_step_matrices_match_the_float_steps_for_the_oscillator():
    # For H = (q^2 + p^2)/2 the force is -q; check the matrices against a
    # direct linear step with the same formulas.
    h = 0.1
    q, p = 0.3, -0.7
    m = si.oscillator_step_matrix("symplectic Euler", h)
    p1 = p - h * q
    q1 = q + h * p1
    assert float(m[0][0]) * q + float(m[0][1]) * p == pytest.approx(q1)
    assert float(m[1][0]) * q + float(m[1][1]) * p == pytest.approx(p1)


def test_symplectic_methods_have_bounded_energy_error():
    checks = {100, 1000, 10000}
    for name in ["symplectic Euler", "leapfrog"]:
        step = dict(si.METHODS)[name]
        errs = si.energy_errors(step, 2.0, 0.0, 0.2, 10000, checks)
        assert errs[10000] == pytest.approx(errs[100], rel=0.05)
        assert errs[10000] < 0.2


def test_explicit_euler_and_rk4_drift():
    checks = {100, 10000}
    euler = si.energy_errors(si.explicit_euler, 2.0, 0.0, 0.2, 10000, checks)
    assert euler[10000] > 10
    rk = si.energy_errors(si.rk4, 2.0, 0.0, 0.2, 10000, checks)
    assert rk[10000] > 50 * rk[100]


def test_leapfrog_is_time_reversible():
    q, p = 1.3, 0.4
    q1, p1 = si.leapfrog(q, p, 0.1)
    q0, p0 = si.leapfrog(q1, p1, -0.1)
    assert (q0, p0) == pytest.approx((q, p), abs=1e-14)
