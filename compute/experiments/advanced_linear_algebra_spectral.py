"""The spectral theorem in floating point, and why numerical analysts fear Jordan.

1. A random real symmetric 6 x 6 matrix is diagonalised by numpy's eigh: the
   computed eigenvectors are orthonormal and A = Q diag(w) Q^T to rounding error.
2. The largest eigenvalue is the maximum of the Rayleigh quotient <Av, v>/<v, v>
   (the variational step in the lesson's proof): random sampling approaches it
   from below and never exceeds it.
3. A non-normal matrix has eigenvectors far from orthogonal.
4. Perturbing a symmetric matrix by size eps moves its eigenvalues by at most
   eps (Weyl's inequality), but perturbing one entry of the 8 x 8 Jordan block
   J8(0) by eps = 1e-10 moves its eigenvalues to modulus eps^(1/8) = 0.056,
   more than five hundred million times further.

All results are floating-point (numerical) evidence about specific matrices.
"""

import numpy as np

EXPERIMENT = {
    "id": "advanced_linear_algebra_spectral",
    "title": "Spectral theorem in floating point; the fragility of Jordan",
    "evidence": ["numerical", "experimental"],
    "lessons": ["advanced-linear-algebra"],
    "summary": (
        "Diagonalises a seeded random symmetric matrix with orthonormal "
        "eigenvectors, checks the Rayleigh-quotient characterisation of the top "
        "eigenvalue by random sampling, measures the angle between eigenvectors "
        "of a non-normal matrix, and contrasts the stability of symmetric "
        "eigenvalues (Weyl) with the eps^(1/n) sensitivity of a Jordan block. "
        "Floating-point evidence, not proof."
    ),
    "packages": ["numpy"],
}


def random_symmetric(n, seed):
    """A seeded random real symmetric n x n matrix (M + M^T) / 2."""
    m = np.random.default_rng(seed).standard_normal((n, n))
    return (m + m.T) / 2


def spectral_residuals(a):
    """(max |Q^T Q - I|, max |A - Q diag(w) Q^T|) for numpy's eigh."""
    w, q = np.linalg.eigh(a)
    n = a.shape[0]
    return (np.abs(q.T @ q - np.eye(n)).max(),
            np.abs(a - q @ np.diag(w) @ q.T).max())


def rayleigh_max(a, samples, seed):
    """Largest Rayleigh quotient <Av, v>/<v, v> over random vectors v."""
    v = np.random.default_rng(seed).standard_normal((samples, a.shape[0]))
    return float(np.max(np.einsum("ij,jk,ik->i", v, a, v) /
                        np.einsum("ij,ij->i", v, v)))


def eigenvector_angle_degrees(a):
    """Angle between the two eigenvector lines of a 2 x 2 matrix."""
    _, vecs = np.linalg.eig(a)
    c = abs(vecs[:, 0] @ vecs[:, 1])
    c /= np.linalg.norm(vecs[:, 0]) * np.linalg.norm(vecs[:, 1])
    return float(np.degrees(np.arccos(min(1.0, c))))


def perturbed_jordan(n, eps):
    """The nilpotent Jordan block J_n(0) with eps in the bottom-left corner.

    Its characteristic polynomial is x^n - eps, so its eigenvalues are the
    n complex n-th roots of eps, all of modulus eps^(1/n).
    """
    j = np.diag(np.ones(n - 1), 1)
    j[n - 1, 0] = eps
    return j


def max_eigenvalue_shift_symmetric(a, eps, seed):
    """Largest change in sorted eigenvalues after a symmetric eps-perturbation."""
    e = random_symmetric(a.shape[0], seed)
    e *= eps / np.linalg.norm(e, 2)
    return float(np.abs(np.linalg.eigvalsh(a + e) -
                        np.linalg.eigvalsh(a)).max())


def main():
    a = random_symmetric(6, 2024)
    orth, recon = spectral_residuals(a)
    w = np.linalg.eigvalsh(a)
    print("1. A random symmetric 6 x 6 matrix A (seed 2024)")
    print("   eigenvalues:", " ".join(f"{x:.4f}" for x in w))
    print(f"   max |Q^T Q - I| = {orth:.1e},  max |A - Q D Q^T| = {recon:.1e}")
    print()
    r = rayleigh_max(a, 20000, 1)
    print("2. Rayleigh quotient over 20000 random vectors")
    print(f"   best found {r:.6f} <= largest eigenvalue {w[-1]:.6f}")
    print()
    print("3. Eigenvector angle (90 degrees for symmetric matrices)")
    for name, m in [("[[2, 1], [1, 2]]", [[2, 1], [1, 2]]),
                    ("[[1, 10], [0, 2]]", [[1, 10], [0, 2]])]:
        ang = eigenvector_angle_degrees(np.array(m, dtype=float))
        print(f"   {name:<18} angle = {ang:6.2f} degrees")
    print()
    eps = 1e-10
    print(f"4. Sensitivity to a perturbation of size eps = {eps:.0e}")
    shift = max_eigenvalue_shift_symmetric(a, eps, 5)
    print(f"   symmetric A + E: eigenvalues move by {shift:.1e} <= eps")
    for n in (2, 4, 8):
        mods = np.abs(np.linalg.eigvals(perturbed_jordan(n, eps)))
        print(f"   J{n}(0) + eps corner: |eigenvalues| = {mods.mean():.2e}"
              f"  (eps^(1/{n}) = {eps ** (1 / n):.2e})")
    print()
    print("Epistemic status: floating-point computations on specific matrices.\n"
          "They illustrate, but do not prove, the spectral theorem, the\n"
          "variational principle and Weyl's inequality (all theorems). The\n"
          "eps^(1/n) law for the Jordan block is exact algebra (x^n = eps); the\n"
          "computer only confirms it numerically.")


if __name__ == "__main__":
    main()
