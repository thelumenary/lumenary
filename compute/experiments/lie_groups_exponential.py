"""The matrix exponential: rotations, determinants, commutators and SL(2, R).

1. exp of a skew-symmetric 3 x 3 matrix is a rotation (orthogonal, det 1),
   agrees with Rodrigues' formula and fixes the axis.
2. det(exp X) = e^(tr X), checked on random 4 x 4 matrices.
3. The group commutator exp(tX) exp(tY) exp(-tX) exp(-tY) equals
   I + t^2 [X, Y] up to an error of order t^3: the Lie bracket measures how
   far the flows fail to commute.
4. In SL(2, R) every exponential exp(X) (X of trace 0) has trace >= -2, so
   diag(-2, -1/2), of trace -5/2, is not an exponential.
The exponential is computed by scaling and squaring a Taylor series.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "lie_groups_exponential",
    "title": "The matrix exponential: rotations, commutators and SL(2, R)",
    "evidence": ["numerical", "experimental"],
    "lessons": ["lie-groups"],
    "summary": (
        "Computes matrix exponentials numerically: exp of a skew-symmetric matrix "
        "is a rotation given by Rodrigues' formula; det exp X = e^(tr X); the "
        "group commutator of exp(tX) and exp(tY) is I + t^2 [X, Y] + O(t^3); and "
        "random samples of exp(sl(2, R)) never have trace below -2, so "
        "diag(-2, -1/2) is not an exponential. Numerical and sampled evidence."
    ),
    "packages": ["numpy"],
}


def expm(a, terms=20):
    """Matrix exponential by scaling, a Taylor polynomial, and squaring."""
    a = np.asarray(a, dtype=float)
    norm = np.linalg.norm(a, 1)
    s = max(0, int(math.ceil(math.log2(norm))) + 1) if norm > 0 else 0
    b = a / 2**s
    result = np.eye(len(a))
    term = np.eye(len(a))
    for k in range(1, terms):
        term = term @ b / k
        result = result + term
    for _ in range(s):
        result = result @ result
    return result


def hat(v):
    """The skew-symmetric matrix of the cross product with v."""
    x, y, z = v
    return np.array([[0.0, -z, y], [z, 0.0, -x], [-y, x, 0.0]])


def rodrigues(v):
    """Rotation by angle |v| about the axis v: I + sin(t)/t K + (1-cos t)/t^2 K^2."""
    t = np.linalg.norm(v)
    k = hat(v)
    return np.eye(3) + math.sin(t) / t * k + (1 - math.cos(t)) / t**2 * k @ k


def group_commutator_error(x, y, t):
    """|| exp(tX) exp(tY) exp(-tX) exp(-tY) - I - t^2 [X, Y] || (max norm)."""
    g = expm(t * x) @ expm(t * y) @ expm(-t * x) @ expm(-t * y)
    return np.abs(g - np.eye(len(x)) - t**2 * (x @ y - y @ x)).max()


def min_trace_of_sl2_exponentials(samples, scale, seed=2024):
    """Smallest trace of exp(X) over random trace-zero 2 x 2 matrices X."""
    rng = np.random.default_rng(seed)
    best = math.inf
    for _ in range(samples):
        a, b, c = rng.normal(0, scale, 3)
        best = min(best, np.trace(expm([[a, b], [c, -a]])))
    return best


def main():
    v = np.array([0.3, -1.2, 0.8])
    r = expm(hat(v))
    print("1. exp of a skew-symmetric matrix (axis v = (0.3, -1.2, 0.8))")
    print(f"   |R^T R - I| = {np.abs(r.T @ r - np.eye(3)).max():.1e},"
          f"  det R = {np.linalg.det(r):.12f}")
    print(f"   |R - Rodrigues| = {np.abs(r - rodrigues(v)).max():.1e},"
          f"  |R v - v| = {np.abs(r @ v - v).max():.1e}")
    rng = np.random.default_rng(7)
    worst = 0.0
    for _ in range(5):
        x = rng.normal(0, 0.7, (4, 4))
        lhs, rhs = np.linalg.det(expm(x)), math.exp(np.trace(x))
        worst = max(worst, abs(lhs - rhs) / rhs)
    print(f"2. det(exp X) = e^(tr X): largest relative error {worst:.1e}"
          " (5 random X)")
    x = np.array([[0.0, 1.0], [0.0, 0.0]])
    y = np.array([[0.0, 0.0], [1.0, 0.0]])
    print("3. Group commutator of e = [[0,1],[0,0]], f = [[0,0],[1,0]]:")
    for t in [0.1, 0.01, 0.001]:
        err = group_commutator_error(x, y, t)
        print(f"   t = {t:<6} error = {err:.2e}   error / t^3 = {err / t**3:.3f}")
    m = min_trace_of_sl2_exponentials(3000, 2.0)
    print("4. SL(2, R): smallest trace of exp(X) over 3000 random X in sl(2, R):")
    print(f"   {m:.6f} (never below -2)")
    rot = expm([[0.0, -math.pi], [math.pi, 0.0]])
    print(f"   exp([[0, -pi], [pi, 0]]) has trace {np.trace(rot):.6f} (it is -I)")
    print("   diag(-2, -1/2) has det 1 and trace -2.5 < -2: not an exponential.")
    print()
    print("Epistemic status: floating-point computation and random sampling.")
    print("Part 4 is evidence, not proof, that tr exp(X) >= -2 on sl(2, R); the")
    print("lesson proves it from X^2 = -det(X) I. Parts 1-3 illustrate theorems")
    print("proved in the lesson (orthogonality in part 1 also in Lean).")


if __name__ == "__main__":
    main()
