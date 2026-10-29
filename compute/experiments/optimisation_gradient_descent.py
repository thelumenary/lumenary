"""Gradient descent and Newton's method on convex quadratics and least squares.

For f(x) = (1/2) x^T Q x - b^T x with Q symmetric positive definite, the
gradient Q x - b is L-Lipschitz with L = largest eigenvalue of Q. The lesson
proves that gradient descent with step 1/L satisfies
    f(x_k) - f* <= L |x_0 - x*|^2 / (2k),
and for a quadratic with smallest eigenvalue mu > 0 the gap even shrinks
geometrically, at least as fast as (1 - mu/L)^(2k) times the initial gap
(stopped at k = 20, before rounding errors of size 1e-16 dominate). The program compares both bounds with the
actual gaps, shows what happens for step sizes 1/L, 1.9/L and 2.1/L, shows
Newton's method finishing in one step on a quadratic, and fits a straight line
to noisy data by gradient descent on the mean squared error, comparing the
result with the exact normal-equations solution.

Floating-point (numerical) evidence about specific problems.
"""

import numpy as np

EXPERIMENT = {
    "id": "optimisation_gradient_descent",
    "title": "Gradient descent: rates, step sizes, Newton and least squares",
    "evidence": ["numerical"],
    "lessons": ["optimisation"],
    "summary": (
        "Runs gradient descent with step 1/L on a convex quadratic and compares "
        "the gap f(x_k) - f* with the proved O(1/k) bound and the geometric "
        "rate for strongly convex functions, tries step sizes beyond 2/L, shows "
        "Newton's method solving a quadratic in one step, and fits a line to "
        "seeded noisy data by gradient descent. Numerical evidence."
    ),
    "packages": ["numpy"],
}

Q = np.array([[3.0, 2.0], [2.0, 6.0]])
B = np.array([1.0, -2.0])
X0 = np.array([4.0, 3.0])


def f(x):
    """The quadratic (1/2) x^T Q x - b^T x."""
    return 0.5 * x @ Q @ x - B @ x


def grad(x):
    return Q @ x - B


def gradient_descent(x0, step, iters, gradient=grad):
    """Iterates x_{k+1} = x_k - step * gradient(x_k); returns all iterates."""
    xs = [np.array(x0, dtype=float)]
    for _ in range(iters):
        xs.append(xs[-1] - step * gradient(xs[-1]))
    return xs


def newton_step(x):
    """One Newton step x - Q^{-1} grad(x) for the quadratic."""
    return x - np.linalg.solve(Q, grad(x))


def line_data(seed, n=40):
    """Noisy samples of y = 2x + 1 for x in [0, 1]."""
    rng = np.random.default_rng(seed)
    x = np.linspace(0, 1, n)
    return x, 2 * x + 1 + 0.1 * rng.standard_normal(n)


def fit_line_gd(x, y, iters):
    """Least-squares line by gradient descent on the mean squared error."""
    a = np.column_stack([x, np.ones_like(x)])
    lip = 2 * np.linalg.eigvalsh(a.T @ a / len(x)).max()

    def g(w):
        return 2 * a.T @ (a @ w - y) / len(x)

    return gradient_descent(np.zeros(2), 1 / lip, iters, g)[-1]


def main():
    mu, lip = np.linalg.eigvalsh(Q)
    xstar = np.linalg.solve(Q, B)
    fstar = f(xstar)
    r2 = np.sum((X0 - xstar) ** 2)
    print(f"f(x) = x^T Q x / 2 - b^T x with eigenvalues mu = {mu:.0f},"
          f" L = {lip:.0f}")
    print("   k   gap f(x_k) - f*   bound L|x0-x*|^2/(2k)   (1-mu/L)^(2k) gap0")
    xs = gradient_descent(X0, 1 / lip, 100)
    for k in (1, 2, 5, 10, 20):
        gap = f(xs[k]) - fstar
        print(f"{k:4d}   {gap:14.3e}   {lip * r2 / (2 * k):21.3e}"
              f"   {(1 - mu / lip) ** (2 * k) * (f(X0) - fstar):17.3e}")
    print()
    print("step size   gap after 50 steps")
    for factor in (1.0, 1.9, 2.1):
        gap = f(gradient_descent(X0, factor / lip, 50)[-1]) - fstar
        print(f"{factor:.1f}/L      {gap:12.3e}")
    print()
    print("Newton: one step from x0 lands at x* with error",
          f"{np.abs(newton_step(X0) - xstar).max():.1e}")
    x, y = line_data(2024)
    a = np.column_stack([x, np.ones_like(x)])
    exact = np.linalg.solve(a.T @ a, a.T @ y)
    w = fit_line_gd(x, y, 2000)
    print(f"line fit: normal equations slope {exact[0]:.4f}, intercept"
          f" {exact[1]:.4f}")
    print(f"          gradient descent  slope {w[0]:.4f}, intercept"
          f" {w[1]:.4f}")
    print()
    print("Epistemic status: floating-point computations on specific problems.\n"
          "They illustrate the O(1/k) theorem (proved in the lesson and in\n"
          "Lean, from the descent and convexity inequalities) and the\n"
          "divergence for steps above 2/L; they do not prove them.")


if __name__ == "__main__":
    main()
