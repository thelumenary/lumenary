"""Poisson summation for the Gaussian, and the uncertainty principle.

Poisson summation applied to exp(-pi t x^2) gives Jacobi's identity
theta(t) = t^(-1/2) theta(1/t) for theta(t) = sum over n of exp(-pi n^2 t).
We check it numerically for several t. Then we compute the Heisenberg
uncertainty ratio (int x^2 |f|^2)(int xi^2 |f^|^2) / (||f||^4 / 16 pi^2) for
three functions with known Fourier transforms: it equals 1 for the Gaussian
and exceeds 1 otherwise, as the uncertainty inequality predicts.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "harmonic_analysis_poisson_uncertainty",
    "title": "Theta, Poisson summation and the uncertainty principle",
    "evidence": ["numerical"],
    "lessons": ["harmonic-analysis"],
    "summary": (
        "Checks Jacobi's identity theta(t) = t^(-1/2) theta(1/t), a consequence of "
        "Poisson summation, to floating-point accuracy for several t. Then computes "
        "the Heisenberg uncertainty ratio by numerical integration for a Gaussian "
        "(ratio 1, the extremal case), a two-sided exponential (ratio 2) and a tent "
        "function (ratio 6/5). Numerical checks of proved identities and inequalities."
    ),
    "packages": ["numpy"],
}


def theta(t, terms=60):
    """theta(t) = sum over |n| <= terms of exp(-pi n^2 t), for t > 0."""
    if t <= 0:
        raise ValueError("t must be positive")
    n = np.arange(-terms, terms + 1)
    return float(np.sum(np.exp(-math.pi * n.astype(float) ** 2 * t)))


def trapezoid(values, grid):
    """Trapezoidal rule on a uniform grid."""
    h = grid[1] - grid[0]
    return float(h * (np.sum(values) - 0.5 * (values[0] + values[-1])))


#: Functions f with their Fourier transforms f^(xi) = int f(x) e^(-2 pi i x xi) dx.
EXAMPLES = {
    "Gaussian exp(-pi x^2)": (
        lambda x: np.exp(-math.pi * x ** 2),
        lambda s: np.exp(-math.pi * s ** 2),
    ),
    "exp(-|x|)": (
        lambda x: np.exp(-np.abs(x)),
        lambda s: 2 / (1 + 4 * math.pi ** 2 * s ** 2),
    ),
    "tent max(1 - |x|, 0)": (
        lambda x: np.maximum(1 - np.abs(x), 0),
        lambda s: np.sinc(s) ** 2,
    ),
}


def uncertainty_ratio(f, fhat, half_width=400.0, points=400001):
    """(int x^2 f^2)(int xi^2 fhat^2) divided by ||f||_2^4 / (16 pi^2)."""
    grid = np.linspace(-half_width, half_width, points)
    fx, fs = f(grid), fhat(grid)
    spread_x = trapezoid(grid ** 2 * fx ** 2, grid)
    spread_s = trapezoid(grid ** 2 * fs ** 2, grid)
    norm_sq = trapezoid(fx ** 2, grid)
    return spread_x * spread_s / (norm_sq ** 2 / (16 * math.pi ** 2))


def main():
    print("Jacobi: theta(t) = t^(-1/2) theta(1/t), theta(t) = sum exp(-pi n^2 t)")
    for t in [0.1, 0.5, 1.0, 2.0, 7.0]:
        lhs, rhs = theta(t), theta(1 / t) / math.sqrt(t)
        print(f"  t = {t:>4}: {lhs:.15f}  {rhs:.15f}  diff {abs(lhs - rhs):.1e}")
    print("  (at t = 0.1 the left side needs many terms; the right side, few)")
    print()
    print("Uncertainty: (int x^2|f|^2)(int xi^2|f^|^2) >= ||f||^4 / (16 pi^2)")
    for name, (f, fhat) in EXAMPLES.items():
        print(f"  {name:<22} ratio = {uncertainty_ratio(f, fhat):.4f}")
    print("  Exact values: 1, 2 and 6/5. Equality holds only for Gaussians.")
    print()
    print("Epistemic status: numerical. Jacobi's identity is a theorem (Poisson")
    print("summation); here it is confirmed to about 1e-15 for five values of t.")
    print("The ratios are trapezoidal approximations on [-400, 400] (slowly")
    print("decaying transforms lose a little mass, about 1e-3); the inequality")
    print("itself, ratio >= 1, is proved in the lesson.")


if __name__ == "__main__":
    main()
