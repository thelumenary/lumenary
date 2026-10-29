"""The harmonic oscillator spectrum from a finite-difference Hamiltonian.

In units hbar = m = omega = 1 the Hamiltonian is H = -(1/2) d^2/dx^2 + x^2/2.
We replace it by a symmetric tridiagonal matrix on a grid of N points in
[-L, L] (Dirichlet boundary) and compute its lowest eigenvalues with numpy.
They approach n + 1/2, and halving the grid spacing divides the error by
about 4 (a second-order method). From the ground-state eigenvector we also
compute the uncertainty product sigma_x sigma_p, which is 1/2: the minimum
allowed by the Heisenberg relation.
"""

import numpy as np

EXPERIMENT = {
    "id": "quantum_mechanics_oscillator_spectrum",
    "title": "Harmonic oscillator levels from a finite-difference Hamiltonian",
    "evidence": ["numerical"],
    "lessons": ["quantum-mechanics"],
    "summary": (
        "Discretises H = -(1/2) d^2/dx^2 + x^2/2 on [-8, 8] by central "
        "differences and computes the lowest eigenvalues with numpy for three "
        "grid spacings: they approach n + 1/2 with second-order error. The "
        "ground-state uncertainty product sigma_x sigma_p comes out as 1/2. "
        "Floating-point evidence for a truncated, discretised operator; the "
        "exact spectrum is derived in the lesson with ladder operators."
    ),
    "packages": ["numpy"],
}


def hamiltonian(n_points, half_width):
    """Finite-difference matrix for -(1/2) d^2/dx^2 + x^2/2 and its grid."""
    if n_points < 3:
        raise ValueError("need at least 3 grid points")
    x = np.linspace(-half_width, half_width, n_points)
    h = x[1] - x[0]
    main = 1.0 / h ** 2 + 0.5 * x ** 2
    off = np.full(n_points - 1, -0.5 / h ** 2)
    return np.diag(main) + np.diag(off, 1) + np.diag(off, -1), x


def lowest_levels(n_points, half_width, count):
    """The `count` smallest eigenvalues of the discretised Hamiltonian."""
    matrix, _ = hamiltonian(n_points, half_width)
    return np.linalg.eigvalsh(matrix)[:count]


def ground_state_uncertainty(n_points, half_width):
    """sigma_x * sigma_p for the lowest eigenvector (grid approximation)."""
    matrix, x = hamiltonian(n_points, half_width)
    h = x[1] - x[0]
    # Inverse iteration with a shift just below E_0 = 1/2 (the next level is
    # near 3/2), much faster than a full eigendecomposition: each step shrinks
    # the other components by a factor of about 100.
    shifted = matrix - 0.49 * np.eye(n_points)
    v = np.ones(n_points)
    for _ in range(12):
        v = np.linalg.solve(shifted, v)
        v /= np.linalg.norm(v)
    psi = v / np.sqrt(h)
    mean_x = h * np.sum(x * psi ** 2)
    var_x = h * np.sum((x - mean_x) ** 2 * psi ** 2)
    dpsi = np.gradient(psi, h)
    var_p = h * np.sum(dpsi ** 2)
    return float(np.sqrt(var_x * var_p))


def main():
    half_width, count = 8.0, 6
    print("Lowest eigenvalues of the discretised oscillator (exact: n + 1/2):")
    print("     N       h       E_0       E_1       E_2       E_5")
    errors = []
    for n_points in [161, 321, 641]:
        levels = lowest_levels(n_points, half_width, count)
        h = 2 * half_width / (n_points - 1)
        print(f"  {n_points:>4}   {h:.3f}   {levels[0]:.5f}   {levels[1]:.5f}"
              f"   {levels[2]:.5f}   {levels[5]:.5f}")
        errors.append(abs(levels[5] - 5.5))
    print("error in E_5 for the three grids:",
          ", ".join(f"{e:.2e}" for e in errors))
    print("ratios:", ", ".join(f"{a / b:.2f}" for a, b in zip(errors, errors[1:])),
          "(about 4: the error is O(h^2))")
    print()
    u = ground_state_uncertainty(641, half_width)
    print(f"Ground state: sigma_x * sigma_p = {u:.5f}; the exact value is the")
    print("Heisenberg minimum 1/2 (the difference is discretisation error).")
    print("The spacing E_(n+1) - E_n = 1 = hbar omega is the energy quantum,")
    print("and E_0 = 1/2 is the zero-point energy.")
    print()
    print("Epistemic status: floating-point eigenvalues of a finite matrix")
    print("approximating an unbounded operator on a truncated interval. The")
    print("agreement with n + 1/2 is numerical evidence; the exact spectrum is")
    print("the theorem proved in the lesson.")


if __name__ == "__main__":
    main()
