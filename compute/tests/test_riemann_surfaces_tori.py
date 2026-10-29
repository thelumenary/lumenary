import cmath
import math

import pytest

import riemann_surfaces_tori as rt


def test_sigma():
    assert rt.sigma(3, 1) == 1
    assert rt.sigma(3, 2) == 9
    assert rt.sigma(5, 6) == 1 + 32 + 243 + 7776


def test_special_values():
    assert rt.j_invariant(1j).real == pytest.approx(1728, abs=1e-6)
    rho = cmath.exp(2j * math.pi / 3)
    assert abs(rt.j_invariant(rho)) < 1e-6


@pytest.mark.parametrize("tau", [0.3 + 1.1j, -0.2 + 0.9j, 0.45 + 2.0j])
def test_modular_invariance(tau):
    j = rt.j_invariant(tau, 200)
    assert rt.j_invariant(tau + 1, 200) == pytest.approx(j, rel=1e-9)
    assert rt.j_invariant(-1 / tau, 400) == pytest.approx(j, rel=1e-6)


def test_reduction_lands_in_fundamental_domain():
    for tau in [3.7 + 0.2j, -0.45 + 0.05j, 0.1 + 0.6j, 12.3 + 0.01j]:
        end, steps = rt.reduce_to_fundamental_domain(tau)
        assert abs(end.real) <= 0.5 + 1e-12
        assert abs(end) >= 1 - 1e-9
        assert end.imag > 0


def test_lattice_tau_and_homothety():
    assert rt.lattice_tau(1 + 0j, 1j) == 1j
    assert rt.lattice_tau(1j, 1 + 0j) == 1j  # orientation is normalised
    t = rt.lattice_tau(2 + 2j, -2 + 2j)
    assert rt.j_invariant(t).real == pytest.approx(1728, abs=1e-6)
