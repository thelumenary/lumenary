"""Galerkin finite elements for -u'' = f on (0, 1), u(0) = u(1) = 0.

The weak formulation asks for u in H^1_0 with int u'v' = int f v for all v.
Galerkin's method imposes this only for v in the space of continuous
piecewise-linear "hat" functions on a uniform mesh of width h = 1/N, giving
the tridiagonal system (1/h) tridiag(-1, 2, -1) U = F. For f = pi^2 sin(pi x)
(exact solution sin(pi x)) we measure the errors: the energy error falls like
h, the L^2 error like h^2, and in one dimension the nodal values are exact.
We also check the discrete maximum principle: the inverse of the stiffness
matrix has positive entries, so f >= 0 gives U >= 0.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "pde_theory_galerkin_fem",
    "title": "Finite elements: Galerkin's method for -u'' = f",
    "evidence": ["numerical"],
    "lessons": ["pde-theory"],
    "summary": (
        "Solves the weak form of -u'' = pi^2 sin(pi x), u(0) = u(1) = 0, by "
        "piecewise-linear finite elements for N = 4 to 64 elements. The energy "
        "error halves and the L^2 error quarters when h halves (rates 1 and 2), "
        "the nodal values agree with sin(pi x) to rounding error, and the "
        "stiffness matrix has a positive inverse (discrete maximum principle). "
        "Numerical evidence for one problem; Lax-Milgram and Cea's lemma explain it."
    ),
    "packages": ["numpy"],
}

GAUSS_X, GAUSS_W = np.polynomial.legendre.leggauss(6)


def stiffness(n):
    """The (n-1) x (n-1) matrix int phi_i' phi_j' = (1/h) tridiag(-1, 2, -1)."""
    if n < 2:
        raise ValueError("need at least 2 elements")
    h = 1 / n
    main = 2 * np.ones(n - 1)
    off = -np.ones(n - 2)
    return (np.diag(main) + np.diag(off, 1) + np.diag(off, -1)) / h


def load(n):
    """F_i = int f phi_i for f = pi^2 sin(pi x), computed exactly."""
    h = 1 / n
    nodes = np.arange(1, n) * h
    return 2 * (1 - math.cos(math.pi * h)) * np.sin(math.pi * nodes) / h


def solve(n):
    """Nodal values (including the zero boundary values) of the Galerkin
    solution with n elements."""
    interior = np.linalg.solve(stiffness(n), load(n))
    return np.concatenate([[0.0], interior, [0.0]])


def errors(n):
    """(energy error, L^2 error) of the Galerkin solution, by Gauss
    quadrature on each element; the exact solution is sin(pi x)."""
    values = solve(n)
    h = 1 / n
    energy = l2 = 0.0
    for i in range(n):
        a = i * h
        x = a + h * (GAUSS_X + 1) / 2
        w = GAUSS_W * h / 2
        slope = (values[i + 1] - values[i]) / h
        uh = values[i] + slope * (x - a)
        energy += np.sum(w * (math.pi * np.cos(math.pi * x) - slope) ** 2)
        l2 += np.sum(w * (np.sin(math.pi * x) - uh) ** 2)
    return math.sqrt(energy), math.sqrt(l2)


def nodal_error(n):
    """Largest error of the Galerkin solution at the mesh nodes."""
    nodes = np.arange(n + 1) / n
    return float(np.max(np.abs(solve(n) - np.sin(math.pi * nodes))))


def main():
    print("-u'' = pi^2 sin(pi x) on (0, 1), u(0) = u(1) = 0; exact u = sin(pi x)")
    print(f"{'N':>4} {'energy err':>11} {'ratio':>6} {'L2 err':>11} {'ratio':>6}"
          f" {'nodal err':>10}")
    previous = None
    for n in [4, 8, 16, 32, 64]:
        e1, e0 = errors(n)
        r1 = f"{previous[0] / e1:6.2f}" if previous else "     -"
        r0 = f"{previous[1] / e0:6.2f}" if previous else "     -"
        print(f"{n:>4} {e1:>11.3e} {r1} {e0:>11.3e} {r0} {nodal_error(n):>10.1e}")
        previous = (e1, e0)
    print("Halving h halves the energy error (rate 1) and quarters the L^2")
    print("error (rate 2); in 1D the nodal values are exact up to rounding.")
    print()
    inverse = np.linalg.inv(stiffness(16))
    print("Discrete maximum principle, N = 16:")
    print(f"  smallest entry of the inverse stiffness matrix: {inverse.min():.4f}")
    print("  all entries positive, so f >= 0 forces U >= 0")
    print()
    print("Epistemic status: numerical evidence for one smooth right-hand side")
    print("and five meshes. That the energy error is O(h) follows from Cea's")
    print("lemma (Lax-Milgram stability) plus interpolation estimates, the L^2")
    print("rate from a duality argument, and positivity from the M-matrix")
    print("structure; this table illustrates those theorems but proves none.")


if __name__ == "__main__":
    main()
