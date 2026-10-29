import math

import numpy as np
import pytest

import pde_theory_galerkin_fem as fem


def test_stiffness_matrix_structure():
    k = fem.stiffness(4)
    assert k.shape == (3, 3)
    assert np.allclose(k, k.T)
    assert np.allclose(k, 4 * np.array([[2, -1, 0], [-1, 2, -1], [0, -1, 2]]))
    assert np.all(np.linalg.eigvalsh(k) > 0)
    with pytest.raises(ValueError):
        fem.stiffness(1)


def test_inverse_is_green_function_and_positive():
    n = 10
    inverse = np.linalg.inv(fem.stiffness(n))
    nodes = np.arange(1, n) / n
    green = np.minimum.outer(nodes, nodes) * (1 - np.maximum.outer(nodes, nodes))
    assert np.allclose(inverse, green)
    assert inverse.min() > 0


def test_nodal_values_exact():
    for n in [3, 7, 20]:
        assert fem.nodal_error(n) < 1e-12


def test_convergence_rates():
    e1a, e0a = fem.errors(16)
    e1b, e0b = fem.errors(32)
    assert e1a / e1b == pytest.approx(2.0, abs=0.05)
    assert e0a / e0b == pytest.approx(4.0, abs=0.1)


def test_energy_error_formula_small_h():
    # Interpolation error: ||e'||^2 ~ (h^2/12) int |u''|^2 = h^2 pi^4 / 24.
    e1, _ = fem.errors(64)
    assert e1 == pytest.approx(math.pi ** 2 / 64 / math.sqrt(24), rel=1e-2)


def test_boundary_values_zero():
    values = fem.solve(8)
    assert values[0] == 0 and values[-1] == 0
    assert len(values) == 9
