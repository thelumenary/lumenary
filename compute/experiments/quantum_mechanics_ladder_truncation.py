"""Ladder operators on N levels: where the commutation relation must break.

On the span of the first N oscillator states, the annihilation operator a is
the N x N matrix with sqrt(1), ..., sqrt(N - 1) above the diagonal. We compute
the commutator [a, a^dagger] exactly (its entries are integers): it is the
identity except for the last diagonal entry, 1 - N, which makes the trace 0,
as it must be for any commutator of matrices. With X = (a + a^dagger)/sqrt 2
and P = (a - a^dagger)/(i sqrt 2) we check the Robertson inequality
sigma_X sigma_P >= |<[X, P]>| / 2 for number states and random states.
"""

import math
import random

import numpy as np

EXPERIMENT = {
    "id": "quantum_mechanics_ladder_truncation",
    "title": "Truncated ladder operators and the uncertainty relation",
    "evidence": ["exact", "numerical"],
    "lessons": ["quantum-mechanics"],
    "summary": (
        "Builds the N-level ladder matrices, computes [a, a^dagger] exactly "
        "(diag(1, ..., 1, 1 - N), trace 0: the canonical commutation relation "
        "cannot hold in finite dimensions), confirms that a^dagger a has "
        "eigenvalues 0, ..., N - 1, and checks the Robertson uncertainty "
        "inequality for number states and 200 seeded random states. A finite "
        "check of theorems proved in the lesson."
    ),
    "packages": ["numpy"],
}


def ladder_commutator_diagonal(n_levels):
    """Diagonal of [a, a^dagger] computed exactly: entries (k+1) - k, last 1-N."""
    if n_levels < 1:
        raise ValueError("need at least one level")
    a_ad = [k + 1 if k < n_levels - 1 else 0 for k in range(n_levels)]
    ad_a = list(range(n_levels))
    return [p - q for p, q in zip(a_ad, ad_a)]


def annihilation(n_levels):
    """The N x N annihilation matrix a (complex)."""
    return np.diag(np.sqrt(np.arange(1, n_levels)), 1).astype(complex)


def position_momentum(n_levels):
    """X = (a + a^dagger)/sqrt(2), P = (a - a^dagger)/(i sqrt(2))."""
    a = annihilation(n_levels)
    ad = a.conj().T
    return (a + ad) / math.sqrt(2), (a - ad) / (1j * math.sqrt(2))


def robertson_sides(state, x_op, p_op):
    """(sigma_X * sigma_P, |<[X, P]>| / 2) for a normalised state vector."""
    def mean(op):
        return np.vdot(state, op @ state)
    var_x = (mean(x_op @ x_op) - mean(x_op) ** 2).real
    var_p = (mean(p_op @ p_op) - mean(p_op) ** 2).real
    comm = mean(x_op @ p_op - p_op @ x_op)
    return math.sqrt(max(var_x, 0) * max(var_p, 0)), abs(comm) / 2


def main():
    n = 8
    diag = ladder_commutator_diagonal(n)
    print(f"N = {n}: diagonal of [a, a^dagger] = {diag}")
    print(f"trace = {sum(diag)} (a commutator of matrices always has trace 0)")
    a = annihilation(n)
    number = np.linalg.eigvalsh(a.conj().T @ a)
    print("eigenvalues of a^dagger a:",
          " ".join(f"{float(v):.3f}" for v in number))
    x_op, p_op = position_momentum(n)
    print()
    print("Number states |k>: sigma_X sigma_P versus |<[X,P]>|/2")
    for k in range(n):
        state = np.zeros(n, dtype=complex)
        state[k] = 1
        lhs, rhs = robertson_sides(state, x_op, p_op)
        print(f"  k = {k}: {lhs:.4f} >= {rhs:.4f}")
    print("For k < N - 1 these are k + 1/2 >= 1/2, as for the true oscillator;")
    print("the top level feels the truncation: <[X, P]> = i(1 - N) there.")
    rng = random.Random(1925)
    worst = math.inf
    for _ in range(200):
        v = np.array([complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(n)])
        v /= np.linalg.norm(v)
        lhs, rhs = robertson_sides(v, x_op, p_op)
        worst = min(worst, lhs - rhs)
    print(f"200 random states: min of sigma_X sigma_P - |<[X,P]>|/2 = {worst:.4f}")
    print()
    print("Epistemic status: the commutator diagonal is exact integer")
    print("arithmetic; the eigenvalues and uncertainty products are floating")
    print("point for one N and finitely many states. Robertson's inequality")
    print("and the trace argument are proved in the lesson and in Lean.")


if __name__ == "__main__":
    main()
