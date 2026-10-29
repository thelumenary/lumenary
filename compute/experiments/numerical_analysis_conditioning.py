"""Conditioning, pivoting and least squares in floating point.

Four numerical experiments in IEEE double precision (unit roundoff
u = 2^-53, about 1.1e-16). (1) Hilbert matrices H_ij = 1/(i + j - 1) are
notoriously ill conditioned: solving H x = b with a backward-stable solver
gives a relative error of roughly kappa(H) u, as the perturbation bound
predicts. (2) Gaussian elimination without pivoting on [[1e-20, 1], [1, 1]]
returns a wrong answer although the matrix is well conditioned; with
partial pivoting the answer is right. (3) Wilkinson's matrix makes partial
pivoting's growth factor equal 2^(n-1), the worst case. (4) For Lauchli's
least-squares problem the normal equations A^T A x = A^T b are exactly
singular in floating point, while a QR factorisation solves it accurately.

Evidence: numerical (floating point), compared with exact solutions.
"""

import numpy as np

EXPERIMENT = {
    "id": "numerical_analysis_conditioning",
    "title": "Conditioning, pivoting and least squares in floating point",
    "evidence": ["numerical", "counterexample"],
    "lessons": ["numerical-analysis"],
    "summary": (
        "Solves Hilbert systems and compares the error with kappa(H) times the "
        "unit roundoff; shows elimination without pivoting failing on "
        "[[1e-20, 1], [1, 1]] while partial pivoting succeeds; measures the "
        "growth factor 2^(n-1) on Wilkinson's matrix; and shows the normal "
        "equations breaking down on Lauchli's least-squares problem while QR "
        "works. Floating-point evidence."
    ),
    "packages": ["numpy"],
}

UNIT_ROUNDOFF = 2.0 ** -53


def hilbert(n):
    """The n x n Hilbert matrix."""
    i = np.arange(1, n + 1)
    return 1.0 / (i[:, None] + i[None, :] - 1)


def lu_solve(a, b, pivot=True):
    """Solve a x = b by Gaussian elimination (optionally partial pivoting).

    Returns (x, growth) where growth = max |U_ij| / max |A_ij|.
    """
    a = np.array(a, dtype=float)
    b = np.array(b, dtype=float)
    n = len(b)
    scale = np.max(np.abs(a))
    for k in range(n - 1):
        if pivot:
            p = k + int(np.argmax(np.abs(a[k:, k])))
            a[[k, p]] = a[[p, k]]
            b[[k, p]] = b[[p, k]]
        for i in range(k + 1, n):
            m = a[i, k] / a[k, k]
            a[i, k:] -= m * a[k, k:]
            b[i] -= m * b[k]
    x = np.zeros(n)
    for i in range(n - 1, -1, -1):
        x[i] = (b[i] - a[i, i + 1:] @ x[i + 1:]) / a[i, i]
    growth = np.max(np.abs(np.triu(a))) / scale
    return x, growth


def wilkinson(n):
    """1 on the diagonal and last column, -1 below the diagonal."""
    a = np.eye(n) - np.tril(np.ones((n, n)), -1)
    a[:, -1] = 1.0
    return a


def lauchli(eps):
    """Lauchli's 3 x 2 matrix [[1, 1], [eps, 0], [0, eps]]."""
    return np.array([[1.0, 1.0], [eps, 0.0], [0.0, eps]])


def rel_err(x, exact):
    """Relative error in the max norm."""
    return np.max(np.abs(x - exact)) / np.max(np.abs(exact))


def main():
    print("1. Hilbert systems H x = b with exact x = (1, ..., 1)")
    print("    n     kappa(H)   rel. error   kappa * u")
    for n in [4, 6, 8, 10, 12]:
        h = hilbert(n)
        x = np.linalg.solve(h, h @ np.ones(n))
        k = np.linalg.cond(h)
        print(f"   {n:2d}   {k:10.2e}   {rel_err(x, np.ones(n)):10.2e}"
              f"   {k * UNIT_ROUNDOFF:9.2e}")
    print()
    a, b = [[1e-20, 1.0], [1.0, 1.0]], [1.0, 2.0]
    x0, _ = lu_solve(a, b, pivot=False)
    x1, _ = lu_solve(a, b, pivot=True)
    print("2. [[1e-20, 1], [1, 1]] x = (1, 2); exact x = (1, 1) to 20 digits")
    print(f"   no pivoting:      x = ({x0[0]:.6f}, {x0[1]:.6f})")
    print(f"   partial pivoting: x = ({x1[0]:.6f}, {x1[1]:.6f})")
    print()
    print("3. Growth factor of partial pivoting on Wilkinson's matrix")
    for n in [10, 30, 55]:
        w = wilkinson(n)
        xs = np.linspace(1.0, 2.0, n)
        x, g = lu_solve(w, w @ xs)
        print(f"   n = {n:2d}: growth {g:9.3e} = 2^{np.log2(g):.0f},"
              f" rel. error {rel_err(x, xs):.1e}")
    print()
    eps = 1e-8
    m = lauchli(eps)
    rhs = m @ np.array([1.0, 1.0])
    gram = m.T @ m
    q, r = np.linalg.qr(m)
    xq = np.linalg.solve(r, q.T @ rhs)
    print("4. Lauchli least squares, eps = 1e-8, exact x = (1, 1)")
    print(f"   computed A^T A = {gram.tolist()}: det = {np.linalg.det(gram):.1e}")
    print(f"   QR solution: ({xq[0]:.8f}, {xq[1]:.8f})")
    print()
    print("Epistemic status: numerical experiments in IEEE double precision.")
    print("They illustrate the perturbation bound, the need for pivoting, the")
    print("worst-case growth factor and the squaring of the condition number")
    print("by the normal equations; the theorems themselves are in the lesson.")


if __name__ == "__main__":
    main()
