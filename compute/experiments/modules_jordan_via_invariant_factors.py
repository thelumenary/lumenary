"""Jordan normal form from the structure theorem over Q[x].

A square matrix A makes Q^n into a Q[x]-module (x acts by A), presented by
the matrix xI - A. Its invariant factors d1 | d2 | ... | dn are quotients of
determinantal divisors: D_k = monic gcd of the k x k minors of xI - A, and
d_k = D_k / D_(k-1). Each power (x - c)^e in the d_k is a Jordan block of
size e for the eigenvalue c. We compute the blocks this way and compare them
with sympy's independent jordan_form; an irreducible factor such as x^2 + 1
shows a module with no Jordan form over Q. Exact symbolic computation.
"""

from itertools import combinations

import sympy as sp

EXPERIMENT = {
    "id": "modules_jordan_via_invariant_factors",
    "title": "Jordan blocks from invariant factors over Q[x]",
    "evidence": ["symbolic", "exact"],
    "lessons": ["modules"],
    "summary": (
        "Computes the invariant factors of the Q[x]-module defined by a matrix "
        "from the gcds of minors of xI - A, predicts the Jordan blocks from "
        "the prime-power factors, and compares with sympy's jordan_form for "
        "four matrices, including two nilpotent matrices with the same "
        "characteristic and different module structure. Exact symbolic "
        "checks of examples, not a proof."
    ),
    "packages": ["sympy"],
}

X = sp.Symbol("x")


def invariant_factors(rows):
    """Invariant factors d_1 | ... | d_n of the Q[x]-module Q^n, x acting by A."""
    a = sp.Matrix(rows)
    n = a.shape[0]
    m = X * sp.eye(n) - a
    divisors = [sp.Integer(1)]
    for k in range(1, n + 1):
        g = sp.Integer(0)
        for r in combinations(range(n), k):
            for c in combinations(range(n), k):
                g = sp.gcd(g, m.extract(list(r), list(c)).det())
        divisors.append(sp.Poly(g, X).monic().as_expr())
    return [sp.factor(sp.cancel(divisors[k] / divisors[k - 1]))
            for k in range(1, n + 1)]


def predicted_blocks(factors):
    """Sorted (eigenvalue, size) pairs from linear prime powers; None if a
    factor does not split into linear factors over Q."""
    blocks = []
    for d in factors:
        for p, e in sp.factor_list(d, X)[1]:
            if sp.degree(p, X) != 1:
                return None
            blocks.append((sp.solve(p, X)[0], e))
    return sorted(blocks)


def sympy_blocks(rows):
    """Sorted (eigenvalue, size) pairs read off sympy's Jordan form."""
    _, j = sp.Matrix(rows).jordan_form()
    n, blocks, i = j.shape[0], [], 0
    while i < n:
        size = 1
        while i + size < n and j[i + size - 1, i + size] == 1:
            size += 1
        blocks.append((j[i, i], size))
        i += size
    return sorted(blocks)


def main():
    examples = {
        "A (4x4, eigenvalues 1, 2, 4)": [[5, 4, 2, 1], [0, 1, -1, -1],
                                         [-1, -1, 3, 0], [1, 1, -1, 2]],
        "N1 (nilpotent)": [[0, 1, 0, 0], [0, 0, 0, 0],
                           [0, 0, 0, 1], [0, 0, 0, 0]],
        "N2 (nilpotent)": [[0, 1, 0, 0], [0, 0, 1, 0],
                           [0, 0, 0, 0], [0, 0, 0, 0]],
        "R (rotation by 90 degrees)": [[0, -1], [1, 0]],
    }
    for name, rows in examples.items():
        factors = invariant_factors(rows)
        shown = ", ".join(str(f) for f in factors if f != 1)
        print(f"{name}:")
        print(f"  invariant factors (non-unit): {shown}")
        pred = predicted_blocks(factors)
        if pred is None:
            print("  a factor is irreducible of degree > 1: no Jordan form "
                  "over Q")
        else:
            agree = pred == sympy_blocks(rows)
            print(f"  blocks (eigenvalue, size): {pred}; sympy agrees: {agree}")
    print("N1 and N2 have the same characteristic polynomial x**4 but are "
          "not similar.")
    print()
    print("Epistemic status: exact symbolic computation for four matrices; "
          "it checks the\nrecipe 'Jordan blocks = prime powers in the "
          "invariant factors' on examples.\nThe recipe is a theorem: the "
          "structure theorem over the PID Q[x], in the lesson.")


if __name__ == "__main__":
    main()
