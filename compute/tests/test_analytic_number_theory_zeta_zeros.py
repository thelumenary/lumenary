import cmath
import math

import analytic_number_theory_zeta_zeros as zz


def test_zeta_special_values():
    assert abs(zz.zeta(2) - math.pi ** 2 / 6) < 1e-12
    assert abs(zz.zeta(4) - math.pi ** 4 / 90) < 1e-12
    assert abs(zz.zeta(0) + 0.5) < 1e-10           # zeta(0) = -1/2
    assert abs(zz.zeta(-1) + 1 / 12) < 1e-10       # zeta(-1) = -1/12
    assert abs(zz.zeta(-2)) < 1e-10                # a trivial zero


def test_functional_symmetry_on_critical_line():
    # zeta(conj s) = conj zeta(s)
    s = 0.5 + 20j
    assert abs(zz.zeta(s.conjugate()) - zz.zeta(s).conjugate()) < 1e-12


def test_hardy_z_is_real():
    for t in (15.0, 22.3, 41.7):
        val = cmath.exp(1j * zz.theta(t)) * zz.zeta(0.5 + 1j * t)
        assert abs(val.imag) < 1e-8


def test_first_ten_zeros():
    zeros = zz.zeros_on_line(10, 50)
    assert len(zeros) == 10
    assert all(abs(a - b) < 1e-7 for a, b in zip(zeros, zz.KNOWN_ZEROS))
    assert abs(zz.zeta(complex(0.5, zeros[0]))) < 1e-8


def test_riemann_von_mangoldt_count():
    # N(50) = 10; the main term is within 1 of it
    assert abs(zz.riemann_von_mangoldt(50) - 10) < 1


def test_explicit_formula_close_to_psi():
    zeros = zz.KNOWN_ZEROS
    assert abs(zz.psi_exact(10.5) - math.log(2520)) < 1e-12
    for x in (7.5, 10.5, 15.5, 20.5):
        assert abs(zz.psi_explicit(x, zeros) - zz.psi_exact(x)) < 0.5
    # with no zeros at all, the approximation is much worse near primes
    assert abs(zz.psi_explicit(10.5, []) - zz.psi_exact(10.5)) > 0.5
