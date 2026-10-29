"""The spectrum of a compact self-adjoint operator, seen through a matrix.

The operator (Gf)(x) = integral of G(x, y) f(y) dy on L^2(0, 1), with kernel
G(x, y) = min(x, y) (1 - max(x, y)), inverts -u'' = f, u(0) = u(1) = 0. It is
compact and self-adjoint, with eigenvalues 1/(k pi)^2 and eigenfunctions
sqrt(2) sin(k pi x). We discretise it by the midpoint rule (an N x N
symmetric matrix), compare its eigenvalues with the exact ones, and count how
they pile up at 0. Then two infinite-dimensional warnings: differentiation is
unbounded, and the sup and L^1 norms are not equivalent.
"""

import math
from fractions import Fraction

import numpy as np

EXPERIMENT = {
    "id": "functional_analysis_compact_spectrum",
    "title": "Eigenvalues of a compact operator, numerically",
    "evidence": ["numerical", "exact"],
    "lessons": ["functional-analysis"],
    "summary": (
        "Discretises the Green's operator of -u'' on (0, 1) by an N x N symmetric "
        "matrix and compares its eigenvalues with the exact 1/(k pi)^2: they agree "
        "to about 2e-6, the eigenvectors are orthonormal, and the eigenvalues "
        "accumulate only at 0. Exact computations show that differentiation has no "
        "bound and that sup and L^1 norms are inequivalent. Numerical evidence for "
        "one operator; the spectral theorem is proved in the lesson."
    ),
    "packages": ["numpy"],
}


def green_matrix(n):
    """Midpoint-rule matrix (1/n) G(x_i, x_j) with x_i = (i + 1/2)/n."""
    if n < 1:
        raise ValueError("n must be positive")
    x = (np.arange(n) + 0.5) / n
    big_x, big_y = np.meshgrid(x, x, indexing="ij")
    kernel = np.minimum(big_x, big_y) * (1 - np.maximum(big_x, big_y))
    return kernel / n


def eigen_decreasing(matrix):
    """Eigenvalues (decreasing) and orthonormal eigenvectors of a symmetric
    matrix."""
    values, vectors = np.linalg.eigh(matrix)
    return values[::-1], vectors[:, ::-1]


def exact_eigenvalue(k):
    """The k-th eigenvalue 1/(k pi)^2 of the Green's operator."""
    return 1 / (k * math.pi) ** 2


def count_above(values, threshold):
    """How many eigenvalues exceed the threshold."""
    return int(np.sum(np.asarray(values) > threshold))


def exact_count_above(threshold):
    """Number of k >= 1 with 1/(k pi)^2 > threshold."""
    k = 0
    while exact_eigenvalue(k + 1) > threshold:
        k += 1
    return k


def derivative_ratio(n, samples=4000):
    """max |f'| / max |f| for f(x) = sin(n x) on [0, 2 pi], sampled."""
    xs = np.linspace(0, 2 * math.pi, samples)
    return float(np.max(np.abs(n * np.cos(n * xs))) /
                 np.max(np.abs(np.sin(n * xs))))


def power_norms(n):
    """Exact (sup norm, L^1 norm) of x^n on [0, 1]."""
    return Fraction(1), Fraction(1, n + 1)


def main():
    n = 200
    values, vectors = eigen_decreasing(green_matrix(n))
    print(f"Green's operator of -u'' on (0, 1), midpoint matrix with N = {n}")
    print(f"{'k':>3} {'matrix':>12} {'exact 1/(k pi)^2':>18} {'rel. error':>11}")
    for k in range(1, 7):
        exact = exact_eigenvalue(k)
        err = abs(values[k - 1] - exact) / exact
        print(f"{k:>3} {values[k - 1]:>12.8f} {exact:>18.8f} {err:>11.1e}")
    orth = np.max(np.abs(vectors.T @ vectors - np.eye(n)))
    print(f"max |V^T V - I| = {orth:.1e} (orthonormal eigenvectors)")
    first = vectors[:, 0] * math.sqrt(n)
    sine = math.sqrt(2) * np.sin(math.pi * (np.arange(n) + 0.5) / n)
    first = first if first @ sine > 0 else -first
    print(f"first eigenvector vs sqrt(2) sin(pi x): max gap "
          f"{np.max(np.abs(first - sine)):.1e}")
    for t in [1e-1, 1e-2, 1e-3]:
        print(f"eigenvalues > {t:g}: matrix {count_above(values, t)}, "
              f"exact {exact_count_above(t)}")
    print(f"smallest matrix eigenvalue: {values[-1]:.2e} (they pile up at 0)")
    print()
    print("Differentiation is unbounded: f = sin(n x), ratio max|f'| / max|f|")
    print("  ", [round(derivative_ratio(m), 3) for m in [1, 10, 100]])
    print("Norms are not equivalent: x^n on [0, 1], (sup norm, L^1 norm)")
    print("  ", [tuple(str(v) for v in power_norms(m)) for m in [1, 10, 100]])
    print()
    print("Epistemic status: the eigenvalue table is a numerical approximation")
    print("of one operator (midpoint rule, floating point), within about 2e-6")
    print("of the exact eigenvalues; it proves nothing in general. The derivative")
    print("ratios are sampled, the norms of x^n exact. That no constant bounds")
    print("either ratio follows because n and n + 1 are unbounded.")


if __name__ == "__main__":
    main()
