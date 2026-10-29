import numpy as np
import pytest

import optimisation_gradient_descent as ogd


def test_quadratic_minimiser():
    xstar = np.linalg.solve(ogd.Q, ogd.B)
    assert np.allclose(ogd.grad(xstar), 0)
    # f is larger anywhere else (Q is positive definite).
    for d in ([1, 0], [0, 1], [1, -1]):
        assert ogd.f(xstar + 0.1 * np.array(d)) > ogd.f(xstar)


def test_rate_bound_holds():
    mu, lip = np.linalg.eigvalsh(ogd.Q)
    xstar = np.linalg.solve(ogd.Q, ogd.B)
    fstar = ogd.f(xstar)
    r2 = np.sum((ogd.X0 - xstar) ** 2)
    xs = ogd.gradient_descent(ogd.X0, 1 / lip, 60)
    gaps = [ogd.f(x) - fstar for x in xs]
    for k in range(1, 61):
        assert gaps[k] <= lip * r2 / (2 * k) + 1e-12
        assert gaps[k] <= gaps[k - 1] + 1e-12  # monotone decrease


def test_step_size_threshold():
    _, lip = np.linalg.eigvalsh(ogd.Q)
    xstar = np.linalg.solve(ogd.Q, ogd.B)
    fstar = ogd.f(xstar)
    converge = ogd.f(ogd.gradient_descent(ogd.X0, 1.9 / lip, 200)[-1]) - fstar
    diverge = ogd.f(ogd.gradient_descent(ogd.X0, 2.1 / lip, 200)[-1]) - fstar
    assert converge < 1e-6
    assert diverge > 1e6


def test_newton_exact_on_quadratic():
    xstar = np.linalg.solve(ogd.Q, ogd.B)
    for x0 in ([0, 0], [10, -7], [1e3, 1e3]):
        assert np.allclose(ogd.newton_step(np.array(x0, dtype=float)), xstar)


def test_line_fit_matches_normal_equations():
    x, y = ogd.line_data(7)
    a = np.column_stack([x, np.ones_like(x)])
    exact = np.linalg.solve(a.T @ a, a.T @ y)
    w = ogd.fit_line_gd(x, y, 3000)
    assert np.allclose(w, exact, atol=1e-6)
    assert exact[0] == pytest.approx(2, abs=0.2)
    assert exact[1] == pytest.approx(1, abs=0.2)
