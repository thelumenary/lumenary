import numpy as np

import numerical_analysis_conditioning as ex


def test_hilbert_matrix_entries_and_conditioning():
    h = ex.hilbert(3)
    assert np.allclose(h, [[1, 1 / 2, 1 / 3], [1 / 2, 1 / 3, 1 / 4], [1 / 3, 1 / 4, 1 / 5]])
    conds = [np.linalg.cond(ex.hilbert(n)) for n in (4, 6, 8)]
    assert conds == sorted(conds) and conds[-1] > 1e10


def test_error_respects_perturbation_bound():
    for n in (4, 6, 8, 10):
        h = ex.hilbert(n)
        x = np.linalg.solve(h, h @ np.ones(n))
        bound = 10 * n * np.linalg.cond(h) * ex.UNIT_ROUNDOFF
        assert ex.rel_err(x, np.ones(n)) <= bound


def test_lu_solve_matches_numpy_on_a_nice_matrix():
    a = np.array([[4.0, -2.0, 1.0], [-2.0, 4.0, -2.0], [1.0, -2.0, 4.0]])
    b = np.array([11.0, -16.0, 17.0])
    for pivot in (True, False):
        x, g = ex.lu_solve(a, b, pivot=pivot)
        assert np.allclose(x, np.linalg.solve(a, b))
        assert g >= 1.0 - 1e-12


def test_pivoting_rescues_tiny_pivot():
    x0, g0 = ex.lu_solve([[1e-20, 1.0], [1.0, 1.0]], [1.0, 2.0], pivot=False)
    x1, g1 = ex.lu_solve([[1e-20, 1.0], [1.0, 1.0]], [1.0, 2.0], pivot=True)
    assert abs(x0[0] - 1.0) > 0.5           # wrong without pivoting
    assert np.allclose(x1, [1.0, 1.0])      # right with pivoting
    assert g0 > 1e19 and g1 <= 2.0


def test_wilkinson_growth_is_two_to_the_n_minus_one():
    for n in (5, 10, 20):
        _, g = ex.lu_solve(ex.wilkinson(n), np.ones(n))
        assert np.isclose(g, 2.0 ** (n - 1))


def test_lauchli_normal_equations_singular_but_qr_fine():
    m = ex.lauchli(1e-8)
    gram = m.T @ m
    assert gram[0, 0] == 1.0 and gram[0, 1] == 1.0  # 1 + eps^2 rounds to 1
    assert np.linalg.matrix_rank(gram) == 1
    q, r = np.linalg.qr(m)
    x = np.linalg.solve(r, q.T @ (m @ np.array([1.0, 1.0])))
    assert np.allclose(x, [1.0, 1.0], atol=1e-6)
