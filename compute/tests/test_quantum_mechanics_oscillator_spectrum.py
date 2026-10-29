import numpy as np
import pytest

import quantum_mechanics_oscillator_spectrum as qo


def test_hamiltonian_is_symmetric_tridiagonal():
    m, x = qo.hamiltonian(11, 2.0)
    assert m.shape == (11, 11) and len(x) == 11
    assert np.allclose(m, m.T)
    assert np.count_nonzero(np.triu(m, 2)) == 0
    with pytest.raises(ValueError):
        qo.hamiltonian(2, 1.0)


def test_levels_approach_n_plus_half():
    levels = qo.lowest_levels(401, 8.0, 5)
    assert np.allclose(levels, np.arange(5) + 0.5, atol=5e-3)
    assert all(b > a for a, b in zip(levels, levels[1:]))


def test_second_order_convergence():
    e1 = abs(qo.lowest_levels(161, 8.0, 3)[2] - 2.5)
    e2 = abs(qo.lowest_levels(321, 8.0, 3)[2] - 2.5)
    assert 3.5 < e1 / e2 < 4.5


def test_ground_state_minimises_uncertainty():
    u = qo.ground_state_uncertainty(641, 8.0)
    assert u == pytest.approx(0.5, abs=1e-3)
