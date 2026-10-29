"""Pascal's triangle three ways, and the binomial theorem checked symbolically.

The number of k-element subsets of an n-element set is computed in three
independent ways - by listing every subset (itertools.combinations), by
Pascal's rule, and by the factorial formula - and the three are compared for
every n up to 12 (listing) or 40 (rule versus formula). The row identities
(symmetry, row sums 2^n, alternating sums 0) are checked on the same range,
and SymPy expands (x + y)^n to confirm that its coefficients are the rows of
the triangle for n up to 12. All of this is exhaustive over a finite range:
evidence for the identities, which the lesson proves for every n.
"""

import itertools
import math

import sympy

EXPERIMENT = {
    "id": "combinatorics_pascal_identities",
    "title": "Pascal's triangle three ways, and the binomial theorem",
    "evidence": ["exhaustive-finite", "exact", "symbolic"],
    "lessons": ["combinatorics"],
    "summary": (
        "Counts k-element subsets by listing them (n <= 12), by Pascal's rule "
        "and by the factorial formula (n <= 40), and checks symmetry, row sums "
        "2^n and alternating row sums 0 on the same range; SymPy confirms that "
        "the coefficients of (x + y)^n are the rows of the triangle for n <= 12. "
        "Exhaustive over a finite range only: the lesson's proofs cover every n."
    ),
    "packages": ["sympy"],
}


def pascal_rows(n_max):
    """Rows 0..n_max of Pascal's triangle, built only from Pascal's rule."""
    rows = [[1]]
    for _ in range(n_max):
        prev = rows[-1]
        rows.append([1] + [prev[k - 1] + prev[k] for k in range(1, len(prev))]
                    + [1])
    return rows


def count_subsets(n, k):
    """Number of k-element subsets of {0, ..., n-1}, by listing them all."""
    return sum(1 for _ in itertools.combinations(range(n), k))


def factorial_formula(n, k):
    """n! / (k! (n - k)!), computed with exact integers."""
    if not 0 <= k <= n:
        return 0
    return math.factorial(n) // (math.factorial(k) * math.factorial(n - k))


def binomial_coefficients(n):
    """Coefficients of x^k y^(n-k), k = 0..n, in SymPy's expansion of (x+y)^n."""
    x, y = sympy.symbols("x y")
    poly = sympy.Poly(sympy.expand((x + y) ** n), x, y)
    return [int(poly.coeff_monomial(x ** k * y ** (n - k)))
            for k in range(n + 1)]


def row_identities_hold(row):
    """Symmetry, row sum 2^n and alternating sum 0 (for n >= 1) for one row."""
    n = len(row) - 1
    alternating = sum((-1) ** k * c for k, c in enumerate(row))
    return (row == row[::-1] and sum(row) == 2 ** n
            and (n == 0 or alternating == 0))


def main():
    rows = pascal_rows(40)
    print("Rows 0-8 of Pascal's triangle (built from Pascal's rule):")
    for n in range(9):
        print(" " * (2 * (8 - n)) + "".join(f"{c:4d}" for c in rows[n]))
    listed = all(count_subsets(n, k) == rows[n][k]
                 for n in range(13) for k in range(n + 1))
    print(f"Listing subsets agrees with the rule for all n <= 12: {listed}")
    formula = all(factorial_formula(n, k) == rows[n][k]
                  for n in range(41) for k in range(n + 1))
    print(f"Factorial formula agrees with the rule for all n <= 40: {formula}")
    rows_ok = all(row_identities_hold(row) for row in rows)
    print(f"Symmetry, sums 2^n, alternating sums 0 (n <= 40): {rows_ok}")
    print(f"Row 40 has {sum(rows[40])} subsets in all = 2^40.")
    expansion = sympy.expand((sympy.Symbol("x") + sympy.Symbol("y")) ** 5)
    print("SymPy expands (x + y)^5 as")
    print(f"  {expansion}")
    sym = all(binomial_coefficients(n) == rows[n] for n in range(13))
    print(f"Coefficients of (x + y)^n = row n for all n <= 12: {sym}")
    print()
    print("Epistemic status: exhaustive checks over a finite range (listing")
    print("subsets for n <= 12, exact integer arithmetic for n <= 40) and a")
    print("symbolic expansion trusted as far as SymPy is. They support, but")
    print("cannot prove, the identities for all n; the lesson's counting and")
    print("induction proofs (checked in Lean) do that.")


if __name__ == "__main__":
    main()
