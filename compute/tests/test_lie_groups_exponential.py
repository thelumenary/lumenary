import math

import numpy as np
import pytest

import lie_groups_exponential as le


def test_expm_matches_known_values():
    assert np.allclose(le.expm(np.zeros((3, 3))), np.eye(3))
    assert np.allclose(le.expm([[1.0, 0], [0, 2.0]]), np.diag([math.e, math.e**2]))
    t = 0.7
    rot = le.expm([[0.0, -t], [t, 0.0]])
    assert np.allclose(rot, [[math.cos(t), -math.sin(t)], [math.sin(t), math.cos(t)]])
    # nilpotent: exp(N) = I + N
    assert np.allclose(le.expm([[0.0, 5.0], [0.0, 0.0]]), [[1, 5], [0, 1]])


def test_skew_exponential_is_rotation():
    v = np.array([1.1, 0.4, -2.0])
    r = le.expm(le.hat(v))
    assert np.allclose(r.T @ r, np.eye(3), atol=1e-12)
    assert np.linalg.det(r) == pytest.approx(1.0)
    assert np.allclose(r, le.rodrigues(v), atol=1e-12)
    assert np.allclose(r @ v, v, atol=1e-12)


def test_hat_is_cross_product():
    a, b = np.array([1.0, 2.0, 3.0]), np.array([-1.0, 0.5, 4.0])
    assert np.allclose(le.hat(a) @ b, np.cross(a, b))


def test_group_commutator_is_second_order():
    x = np.array([[0.0, 1.0], [0.0, 0.0]])
    y = np.array([[0.0, 0.0], [1.0, 0.0]])
    e1 = le.group_commutator_error(x, y, 1e-2)
    e2 = le.group_commutator_error(x, y, 1e-3)
    assert e1 / e2 == pytest.approx(1000, rel=0.05)
    # commuting matrices have trivial group commutator
    d = np.diag([1.0, -1.0])
    assert le.group_commutator_error(d, 2 * d, 0.3) < 1e-12


def test_sl2_exponential_trace_bound():
    assert le.min_trace_of_sl2_exponentials(500, 3.0) >= -2 - 1e-9
    assert np.trace(le.expm([[0.0, -math.pi], [math.pi, 0.0]])) == pytest.approx(-2.0)
