import math

import numpy as np
import pytest

import quantum_mechanics_ladder_truncation as ql


def test_commutator_diagonal_exact():
    for n in range(1, 12):
        d = ql.ladder_commutator_diagonal(n)
        assert sum(d) == 0
        assert d[:-1] == [1] * (n - 1) and d[-1] == 1 - n
    with pytest.raises(ValueError):
        ql.ladder_commutator_diagonal(0)


def test_matrix_commutator_matches_exact_diagonal():
    n = 6
    a = ql.annihilation(n)
    comm = a @ a.conj().T - a.conj().T @ a
    assert np.allclose(comm, np.diag(ql.ladder_commutator_diagonal(n)))


def test_position_momentum_hermitian_and_ccr_except_top():
    n = 7
    x, p = ql.position_momentum(n)
    assert np.allclose(x, x.conj().T) and np.allclose(p, p.conj().T)
    comm = x @ p - p @ x
    expected = 1j * np.diag(ql.ladder_commutator_diagonal(n))
    assert np.allclose(comm, expected)


def test_robertson_holds_and_ground_state_saturates():
    x, p = ql.position_momentum(9)
    ground = np.zeros(9, dtype=complex)
    ground[0] = 1
    lhs, rhs = ql.robertson_sides(ground, x, p)
    assert lhs == pytest.approx(0.5) and rhs == pytest.approx(0.5)
    rng = np.random.default_rng(0)
    for _ in range(50):
        v = rng.normal(size=9) + 1j * rng.normal(size=9)
        v /= np.linalg.norm(v)
        lhs, rhs = ql.robertson_sides(v, x, p)
        assert lhs >= rhs - 1e-12
