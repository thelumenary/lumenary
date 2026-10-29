import numpy as np
import pytest

import advanced_linear_algebra_spectral as als


def test_random_symmetric_is_symmetric_and_seeded():
    a = als.random_symmetric(5, 3)
    assert np.allclose(a, a.T)
    assert np.array_equal(a, als.random_symmetric(5, 3))
    assert not np.array_equal(a, als.random_symmetric(5, 4))


def test_spectral_residuals_are_tiny():
    for seed in range(5):
        orth, recon = als.spectral_residuals(als.random_symmetric(7, seed))
        assert orth < 1e-12 and recon < 1e-12


def test_rayleigh_quotient_never_exceeds_top_eigenvalue():
    a = als.random_symmetric(4, 11)
    top = np.linalg.eigvalsh(a)[-1]
    r = als.rayleigh_max(a, 5000, 2)
    assert r <= top + 1e-12
    assert r > top - 0.5  # in 4 dimensions sampling gets reasonably close
    # For a diagonal matrix the quotient at a coordinate vector is exact.
    d = np.diag([1.0, 5.0, 2.0])
    assert als.rayleigh_max(d, 20000, 0) <= 5.0 + 1e-12


def test_eigenvector_angles():
    assert als.eigenvector_angle_degrees(np.array([[2.0, 1], [1, 2]])) == \
        pytest.approx(90.0)
    # Eigenvectors of [[1, 10], [0, 2]] are (1, 0) and (10, 1).
    expected = np.degrees(np.arctan(1 / 10))
    assert als.eigenvector_angle_degrees(np.array([[1.0, 10], [0, 2]])) == \
        pytest.approx(expected)


def test_perturbed_jordan_eigenvalues_have_modulus_eps_to_one_over_n():
    for n, eps in [(2, 1e-6), (3, 1e-9), (5, 1e-10)]:
        j = als.perturbed_jordan(n, eps)
        assert j[n - 1, 0] == eps and np.trace(j) == 0
        mods = np.abs(np.linalg.eigvals(j))
        assert np.allclose(mods, eps ** (1 / n), rtol=1e-6)


def test_symmetric_perturbations_are_stable_weyl():
    a = als.random_symmetric(6, 2024)
    for eps in (1e-3, 1e-8):
        assert als.max_eigenvalue_shift_symmetric(a, eps, 9) <= eps * (1 + 1e-6)
