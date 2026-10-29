import math
from fractions import Fraction

import numpy as np
import pytest

import functional_analysis_compact_spectrum as fa


def test_green_matrix_is_symmetric_and_positive():
    m = fa.green_matrix(50)
    assert m.shape == (50, 50)
    assert np.allclose(m, m.T)
    values, _ = fa.eigen_decreasing(m)
    assert np.all(values > 0)
    with pytest.raises(ValueError):
        fa.green_matrix(0)


def test_eigenvalues_approximate_exact_ones():
    values, _ = fa.eigen_decreasing(fa.green_matrix(200))
    for k in range(1, 6):
        assert abs(values[k - 1] - fa.exact_eigenvalue(k)) < 1e-5
    assert list(values) == sorted(values, reverse=True)


def test_eigenvectors_orthonormal():
    _, vectors = fa.eigen_decreasing(fa.green_matrix(80))
    assert np.allclose(vectors.T @ vectors, np.eye(80), atol=1e-10)


def test_counts_above_thresholds():
    assert fa.exact_count_above(1e-3) == 10
    assert fa.exact_count_above(1) == 0
    values, _ = fa.eigen_decreasing(fa.green_matrix(200))
    for t in [1e-1, 1e-2, 1e-3]:
        assert fa.count_above(values, t) == fa.exact_count_above(t)
    assert fa.count_above([3, 2, 1], 1.5) == 2


def test_exact_eigenvalue_formula():
    assert fa.exact_eigenvalue(1) == pytest.approx(1 / math.pi ** 2)
    assert fa.exact_eigenvalue(2) == pytest.approx(fa.exact_eigenvalue(1) / 4)


def test_unboundedness_and_inequivalent_norms():
    assert fa.derivative_ratio(1) == pytest.approx(1, rel=1e-3)
    assert fa.derivative_ratio(50) == pytest.approx(50, rel=1e-2)
    sup, l1 = fa.power_norms(9)
    assert sup == 1 and l1 == Fraction(1, 10)
