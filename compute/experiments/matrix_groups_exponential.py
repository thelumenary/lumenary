"""The matrix exponential: rotations, det(exp X) = e^(tr X), and the bracket.

exp(X) = sum X^k / k! is computed here from its power series (with scaling and
squaring, exp(X) = exp(X / 2^s)^(2^s), to keep the series short and accurate).
The experiment checks numerically that

* exp(theta J) is the rotation matrix R(theta), for J = [[0, -1], [1, 0]];
* exp of a skew-symmetric 3 x 3 matrix is orthogonal with determinant 1;
* det(exp X) = e^(tr X) for random matrices (a theorem, not yet in Mathlib);
* exp(X + Y) differs from exp(X) exp(Y) when XY != YX, and for small t
  exp(tX) exp(tY) = exp(t(X + Y) + t^2 [X, Y] / 2 + O(t^3)), the first
  Baker-Campbell-Hausdorff correction. The error orders t^2 and t^3 are read
  off from t = 0.1 and t = 0.01.

Floating-point evidence about specific matrices.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "matrix_groups_exponential",
    "title": "The matrix exponential: rotations, determinants and the bracket",
    "evidence": ["numerical"],
    "lessons": ["matrix-groups"],
    "summary": (
        "Sums the exponential series (with scaling and squaring) to check that "
        "exp(theta J) is a rotation, that exp of a skew-symmetric matrix lies in "
        "SO(3), that det(exp X) = e^(tr X) for seeded random matrices, and that "
        "exp(tX)exp(tY) differs from exp(t(X+Y)) at order t^2, with the "
        "commutator term [X, Y]/2 removing that error. Floating-point evidence."
    ),
    "packages": ["numpy"],
}


def expm(x, terms=20):
    """exp(x) for a square matrix, by scaling and squaring a Taylor series."""
    x = np.asarray(x, dtype=float)
    norm = np.abs(x).sum(axis=1).max()
    s = max(0, int(math.ceil(math.log2(norm))) + 1) if norm > 0 else 0
    y = x / 2 ** s
    result = np.eye(len(x))
    term = np.eye(len(x))
    for k in range(1, terms + 1):
        term = term @ y / k
        result = result + term
    for _ in range(s):
        result = result @ result
    return result


def rotation(theta):
    """The rotation matrix R(theta) of the plane."""
    c, s = math.cos(theta), math.sin(theta)
    return np.array([[c, -s], [s, c]])


def skew(a, b, c):
    """The skew-symmetric matrix with (a, b, c) above the diagonal."""
    return np.array([[0.0, a, b], [-a, 0.0, c], [-b, -c, 0.0]])


def bracket(x, y):
    """The commutator [X, Y] = XY - YX."""
    return x @ y - y @ x


def bch_errors(x, y, t):
    """(|exp(tX)exp(tY) - exp(t(X+Y))|, same with the t^2 [X,Y]/2 term)."""
    lhs = expm(t * x) @ expm(t * y)
    first = np.abs(lhs - expm(t * (x + y))).max()
    second = np.abs(lhs - expm(t * (x + y) + t * t * bracket(x, y) / 2)).max()
    return float(first), float(second)


def main():
    j = np.array([[0.0, -1.0], [1.0, 0.0]])
    err = max(np.abs(expm(th * j) - rotation(th)).max()
              for th in np.linspace(-7, 7, 29))
    print("1. exp(theta J) = R(theta) for 29 angles in [-7, 7]:"
          f" max error {err:.1e}")
    rng = np.random.default_rng(2024)
    worst_orth = worst_det = 0.0
    for _ in range(50):
        q = expm(skew(*rng.uniform(-3, 3, 3)))
        worst_orth = max(worst_orth, np.abs(q.T @ q - np.eye(3)).max())
        worst_det = max(worst_det, abs(np.linalg.det(q) - 1))
    print("2. exp(skew) for 50 random skew-symmetric X:")
    print(f"   max |Q^T Q - I| = {worst_orth:.1e}, max |det Q - 1| ="
          f" {worst_det:.1e}")
    rel = 0.0
    for _ in range(50):
        x = rng.normal(size=(4, 4))
        lhs, rhs = np.linalg.det(expm(x)), math.exp(np.trace(x))
        rel = max(rel, abs(lhs - rhs) / rhs)
    print("3. det(exp X) = e^(tr X) for 50 random 4 x 4 X:"
          f" max relative error {rel:.1e}")
    x = np.array([[0.0, 1.0], [0.0, 0.0]])
    y = np.array([[0.0, 0.0], [1.0, 0.0]])
    gap = np.abs(expm(x + y) - expm(x) @ expm(y)).max()
    print("4. X = [[0, 1], [0, 0]], Y = [[0, 0], [1, 0]] do not commute:")
    print(f"   max |exp(X + Y) - exp(X) exp(Y)| = {gap:.3f}")
    print("   t       without [X,Y]/2   with [X,Y]/2")
    for t in (0.1, 0.01):
        e1, e2 = bch_errors(x, y, t)
        print(f"   {t:<6}  {e1:.2e}          {e2:.2e}")
    print("   (errors shrink like t^2 without the bracket, like t^3 with it)")
    print()
    print("Epistemic status: floating-point computations with a truncated "
          "series.\nThey are numerical evidence for these matrices only. "
          "exp(skew) in SO(n)\nand the one-parameter subgroup law are proved "
          "in the lesson (and in\nLean); det(exp X) = e^(tr X) and the BCH "
          "expansion are theorems proved\nin the references.")


if __name__ == "__main__":
    main()
