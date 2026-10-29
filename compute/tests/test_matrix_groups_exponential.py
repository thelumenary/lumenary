import math

import numpy as np
import pytest

import matrix_groups_exponential as mge


def test_expm_of_zero_and_diagonal():
    assert np.allclose(mge.expm(np.zeros((3, 3))), np.eye(3))
    d = np.diag([1.0, -2.0, 0.5])
    assert np.allclose(mge.expm(d), np.diag(np.exp([1.0, -2.0, 0.5])))


def test_expm_of_nilpotent_is_a_finite_sum():
    n = np.array([[0.0, 3.0], [0.0, 0.0]])
    assert np.allclose(mge.expm(n), np.eye(2) + n)


def test_rotation_generator():
    j = np.array([[0.0, -1.0], [1.0, 0.0]])
    for theta in (0.3, math.pi, 2 * math.pi, -5.0):
        assert np.allclose(mge.expm(theta * j), mge.rotation(theta), atol=1e-12)
    # A full turn returns to the identity.
    assert np.allclose(mge.expm(2 * math.pi * j), np.eye(2), atol=1e-12)


def test_exp_of_skew_is_special_orthogonal():
    for a, b, c in [(0.1, 2.0, -1.0), (3.0, 3.0, 3.0), (0.0, 0.0, 7.0)]:
        x = mge.skew(a, b, c)
        assert np.allclose(x.T, -x)
        q = mge.expm(x)
        assert np.allclose(q.T @ q, np.eye(3), atol=1e-12)
        assert np.linalg.det(q) == pytest.approx(1.0)


def test_det_exp_is_exp_trace():
    rng = np.random.default_rng(0)
    for _ in range(10):
        x = rng.normal(size=(3, 3))
        assert np.linalg.det(mge.expm(x)) == pytest.approx(math.exp(np.trace(x)))


def test_bracket_and_bch_orders():
    x = np.array([[0.0, 1.0], [0.0, 0.0]])
    y = np.array([[0.0, 0.0], [1.0, 0.0]])
    assert np.allclose(mge.bracket(x, y), np.diag([1.0, -1.0]))
    assert np.allclose(mge.bracket(x, x), 0)
    e1a, e2a = mge.bch_errors(x, y, 0.1)
    e1b, e2b = mge.bch_errors(x, y, 0.01)
    assert e1a / e1b == pytest.approx(100, rel=0.05)   # order t^2
    assert e2a / e2b == pytest.approx(1000, rel=0.05)  # order t^3
    # Commuting matrices: no error at all.
    d1, d2 = np.diag([1.0, 2.0]), np.diag([-3.0, 0.5])
    assert max(mge.bch_errors(d1, d2, 0.5)) < 1e-12
