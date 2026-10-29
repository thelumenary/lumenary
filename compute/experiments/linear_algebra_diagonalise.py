"""Which 2 x 2 matrices can be diagonalised? An exhaustive count, and Fibonacci.

Part 1 classifies every 2 x 2 matrix with entries in {-2, ..., 2} (625 of
them) by its characteristic polynomial t^2 - (tr A) t + det A. Two distinct
real eigenvalues: diagonalisable over R. Non-real eigenvalues: diagonalisable
over C only. A repeated eigenvalue: diagonalisable only if A is already the
scalar matrix lambda I. Part 2 diagonalises the Fibonacci matrix with SymPy and
checks Binet's formula exactly for n <= 40. Part 3 shows SymPy's view of the
nilpotent matrix with rows (0, 1), (0, 0): one eigenvalue of algebraic
multiplicity 2 but only one independent eigenvector.
"""

import itertools

import sympy

EXPERIMENT = {
    "id": "linear_algebra_diagonalise",
    "title": "Diagonalisable or not: 625 matrices and the Fibonacci numbers",
    "evidence": ["exhaustive-finite", "symbolic"],
    "lessons": ["linear-algebra"],
    "summary": (
        "Sorts all 625 integer 2 x 2 matrices with entries from -2 to 2 into "
        "real-diagonalisable, complex-only, scalar and defective, using the "
        "discriminant of the characteristic polynomial; then diagonalises the "
        "Fibonacci matrix with SymPy and verifies Binet's formula exactly for "
        "n <= 40, and exhibits a defective (non-diagonalisable) matrix."
    ),
    "packages": ["sympy"],
}


def classify(a, b, c, d):
    """Classify [[a, b], [c, d]] by its eigenvalues.

    Returns 'distinct real', 'complex', 'scalar' or 'defective'.
    """
    trace, det = a + d, a * d - b * c
    disc = trace * trace - 4 * det
    if disc > 0:
        return "distinct real"
    if disc < 0:
        return "complex"
    return "scalar" if (b == 0 and c == 0 and a == d) else "defective"


def census(values):
    """Count the classes over all matrices with entries in ``values``."""
    counts = {"distinct real": 0, "complex": 0, "scalar": 0, "defective": 0}
    for a, b, c, d in itertools.product(values, repeat=4):
        counts[classify(a, b, c, d)] += 1
    return counts


def fibonacci(n):
    """F_0 = 0, F_1 = 1, F_{k+1} = F_k + F_{k-1}, by iteration."""
    x, y = 0, 1
    for _ in range(n):
        x, y = y, x + y
    return x


def binet(n):
    """(phi^n - psi^n) / sqrt(5) as an exact SymPy number."""
    s5 = sympy.sqrt(5)
    phi, psi = (1 + s5) / 2, (1 - s5) / 2
    return sympy.expand((phi**n - psi**n) / s5)


def fibonacci_by_diagonalising(n):
    """The top-right entry of A^n = P D^n P^-1 for A = [[1, 1], [1, 0]]."""
    p, d = sympy.Matrix([[1, 1], [1, 0]]).diagonalize()
    power = p * sympy.diag(d[0, 0] ** n, d[1, 1] ** n) * p.inv()
    return sympy.radsimp(sympy.expand(power[0, 1]))


def multiplicities(rows):
    """[(eigenvalue, algebraic, geometric)] for a SymPy matrix."""
    return [(val, alg, len(vecs))
            for val, alg, vecs in sympy.Matrix(rows).eigenvects()]


def main():
    counts = census(range(-2, 3))
    print("All 625 matrices [[a, b], [c, d]] with entries in -2..2:")
    for label, count in counts.items():
        print(f"  {label:<14} {count:>4}")
    print("  diagonalisable over R:", counts["distinct real"] + counts["scalar"])
    print("  diagonalisable over C:", 625 - counts["defective"])
    print()
    p, d = sympy.Matrix([[1, 1], [1, 0]]).diagonalize()
    print("Fibonacci matrix A = [[1, 1], [1, 0]] = P D P^-1 with")
    print("  D =", list(d.diagonal()))
    print("  A^n = P D^n P^-1, so F_n = (phi^n - psi^n) / sqrt 5")
    ok = all(binet(n) == fibonacci(n) for n in range(41))
    print(f"  Binet's formula equals iteration for n = 0..40: {ok}")
    print(f"  F_40 from A^40 = P D^40 P^-1: {fibonacci_by_diagonalising(40)}")
    print()
    print("N = [[0, 1], [0, 0]]: (eigenvalue, algebraic, geometric) =",
          multiplicities([[0, 1], [0, 0]]))
    print("One independent eigenvector in a 2-dimensional space: N is not")
    print("diagonalisable, exactly as the lesson (and Lean) proves.")
    print()
    print("Epistemic status: part 1 is an exhaustive check of 625 cases using")
    print("the lesson's criterion; part 2 is exact symbolic arithmetic for")
    print("n <= 40 only (the lesson proves Binet's formula for all n); part 3")
    print("trusts SymPy's eigenvector routine, which agrees with the proof.")


if __name__ == "__main__":
    main()
