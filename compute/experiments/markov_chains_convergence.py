"""Convergence to equilibrium: a weather chain forgets where it started.

A three-state chain (dry, cloudy, rainy) has a strictly positive transition
matrix, so it is irreducible and aperiodic. We find its stationary
distribution exactly (rational arithmetic), then follow the distribution mu P^n
from a dry start and measure its total-variation distance to pi. The distance
falls geometrically, at the rate |lambda_2| of the second-largest eigenvalue,
and always below Doeblin's bound (1 - k delta)^n. A periodic chain, by
contrast, never settles down; making it "lazy" restores convergence.
"""

from fractions import Fraction

import numpy as np

EXPERIMENT = {
    "id": "markov_chains_convergence",
    "title": "Convergence to equilibrium, eigenvalues and Doeblin's bound",
    "evidence": ["exact", "numerical"],
    "lessons": ["markov-chains"],
    "summary": (
        "Solves pi P = pi exactly for a 3-state weather chain, then tracks the "
        "total-variation distance between mu P^n and pi: it decays like |lambda_2|^n "
        "and stays below Doeblin's bound (1 - k delta)^n. A periodic two-state chain "
        "oscillates forever, while its lazy version converges. Floating-point powers "
        "of a small matrix; the convergence theorem itself is proved in the lesson."
    ),
    "packages": ["numpy"],
}

STATES = ["dry", "cloudy", "rainy"]
WEATHER = [["3/5", "3/10", "1/10"],
           ["3/10", "2/5", "3/10"],
           ["1/5", "3/10", "1/2"]]


def as_fractions(matrix):
    """Convert a matrix of strings or numbers into Fractions."""
    return [[Fraction(x) for x in row] for row in matrix]


def is_stochastic(matrix):
    """True if all entries are non-negative and every row sums to 1."""
    return all(min(row) >= 0 and sum(row) == 1 for row in matrix)


def stationary_exact(matrix):
    """Solve pi P = pi, sum(pi) = 1 exactly by Gauss-Jordan elimination.

    The equations are pi (P - I) = 0 with one equation replaced by the
    normalisation; for an irreducible chain the solution is unique.
    """
    p = as_fractions(matrix)
    k = len(p)
    # Unknowns pi_0..pi_{k-1}; equation j: sum_i pi_i (P_ij - [i = j]) = 0.
    rows = [[p[i][j] - (1 if i == j else 0) for i in range(k)] + [Fraction(0)]
            for j in range(k)]
    rows[-1] = [Fraction(1)] * k + [Fraction(1)]
    for col in range(k):
        pivot = next(r for r in range(col, k) if rows[r][col] != 0)
        rows[col], rows[pivot] = rows[pivot], rows[col]
        rows[col] = [x / rows[col][col] for x in rows[col]]
        for r in range(k):
            if r != col and rows[r][col] != 0:
                factor = rows[r][col]
                rows[r] = [a - factor * b for a, b in zip(rows[r], rows[col])]
    return [rows[i][k] for i in range(k)]


def tv_distance(mu, nu):
    """Total-variation distance: half the l1 distance."""
    return 0.5 * float(np.abs(np.asarray(mu) - np.asarray(nu)).sum())


def distances(matrix, start, steps):
    """[TV(mu P^n, pi) for n = 0..steps] with mu = the point mass at start."""
    p = np.array([[float(x) for x in row] for row in as_fractions(matrix)])
    pi = np.array([float(x) for x in stationary_exact(matrix)])
    mu = np.zeros(len(p))
    mu[start] = 1.0
    out = []
    for _ in range(steps + 1):
        out.append(tv_distance(mu, pi))
        mu = mu @ p
    return out


def second_eigenvalue(matrix):
    """Largest modulus among the eigenvalues other than 1."""
    p = np.array([[float(x) for x in row] for row in as_fractions(matrix)])
    moduli = sorted(np.abs(np.linalg.eigvals(p)), reverse=True)
    return float(moduli[1])


def main():
    pi = stationary_exact(WEATHER)
    print("Weather chain: stationary distribution (exact)")
    print("  " + ", ".join(f"{s} {x}" for s, x in zip(STATES, pi)))
    lam2 = second_eigenvalue(WEATHER)
    delta = min(min(as_fractions(WEATHER)[i]) for i in range(3))
    factor = 1 - 3 * float(delta)
    print(f"  |lambda_2| = {lam2:.4f}; Doeblin factor 1 - k delta = {factor:.2f}")
    print()
    print("  n   TV(mu P^n, pi)   |lambda_2|^n   Doeblin bound")
    tv = distances(WEATHER, 0, 12)
    for n in [0, 1, 2, 4, 6, 8, 10, 12]:
        print(f"{n:>3} {tv[n]:>16.2e} {lam2 ** n:>14.2e} {factor ** n:>15.2e}")
    print()
    flip = [[0, 1], [1, 0]]
    lazy = [["1/2", "1/2"], ["1/2", "1/2"]]
    print("Periodic chain [[0, 1], [1, 0]] from state 0:",
          [round(d, 2) for d in distances(flip, 0, 5)])
    print("Lazy version (I + P)/2 from state 0:        ",
          [round(d, 2) for d in distances(lazy, 0, 5)])
    print()
    print("Epistemic status: pi is exact. The distances are floating-point")
    print("values for one chain and one starting state; they illustrate the")
    print("convergence theorem, the spectral rate and Doeblin's bound (proved")
    print("in Lean), and the failure of convergence for a periodic chain.")


if __name__ == "__main__":
    main()
