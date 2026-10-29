"""Three ways to compute Fibonacci numbers, and where floating point fails.

The recurrence F(n+2) = F(n+1) + F(n) gives exact integers. Binet's formula
F(n) = (phi^n - psi^n)/sqrt(5) is an exact theorem, but evaluating it with
64-bit floats is not exact: phi and sqrt(5) are rounded, and once F(n) has
more than about 16 significant digits the rounded answer must go wrong. The
generating function x/(1 - x - x^2) gives the same numbers again, by dividing
power series exactly. Finally, the matrix identity
[[1, 1], [1, 0]]^n = [[F(n+1), F(n)], [F(n), F(n-1)]] computes F(n) with only
about log2(n) matrix multiplications, and its determinant gives Cassini's
identity F(n+1)F(n-1) - F(n)^2 = (-1)^n.
"""

import math

EXPERIMENT = {
    "id": "recurrences_generating_functions_binet",
    "title": "Fibonacci numbers: recurrence, Binet, generating function, matrices",
    "evidence": ["exact", "numerical", "exhaustive-finite"],
    "lessons": ["recurrences-generating-functions"],
    "summary": (
        "Computes Fibonacci numbers exactly from the recurrence, from the "
        "generating function x/(1 - x - x^2) by power-series division, and by "
        "repeated squaring of the matrix [[1, 1], [1, 0]]; checks they agree and "
        "that Cassini's identity holds for n < 300; then finds the first n at "
        "which rounding Binet's formula in floating point gives a wrong integer."
    ),
    "packages": [],
}


def fib_list(count):
    """The first `count` Fibonacci numbers F(0), F(1), ..., exactly."""
    out = []
    a, b = 0, 1
    for _ in range(count):
        out.append(a)
        a, b = b, a + b
    return out


def series_divide(num, den, count):
    """First `count` coefficients of num(x)/den(x) as a formal power series.

    `num` and `den` are coefficient lists; den[0] must be 1 so that only
    integer arithmetic is needed. Coefficient n is found from
    num[n] = sum(den[k] * q[n - k]), solved for q[n].
    """
    if not den or den[0] != 1:
        raise ValueError("the denominator must have constant term 1")
    q = []
    for n in range(count):
        c = num[n] if n < len(num) else 0
        for k in range(1, min(n, len(den) - 1) + 1):
            c -= den[k] * q[n - k]
        q.append(c)
    return q


def mat_mul(x, y):
    """Product of 2 x 2 integer matrices given as ((a, b), (c, d))."""
    (a, b), (c, d) = x
    (e, f), (g, h) = y
    return ((a * e + b * g, a * f + b * h), (c * e + d * g, c * f + d * h))


def fib_matrix(n):
    """F(n) from [[1, 1], [1, 0]]^n by repeated squaring; also the multiplications used."""
    if n < 0:
        raise ValueError("n must be non-negative")
    result, power, mults = ((1, 0), (0, 1)), ((1, 1), (1, 0)), 0
    while n:
        if n & 1:
            result, mults = mat_mul(result, power), mults + 1
        n >>= 1
        if n:
            power, mults = mat_mul(power, power), mults + 1
    return result[0][1], mults


def binet_float(n):
    """Binet's formula evaluated in floating point and rounded to an integer."""
    root5 = math.sqrt(5)
    phi, psi = (1 + root5) / 2, (1 - root5) / 2
    return round((phi ** n - psi ** n) / root5)


def first_binet_failure(limit):
    """Smallest n < limit where the rounded float Binet value is wrong, or None."""
    for n, exact in enumerate(fib_list(limit)):
        if binet_float(n) != exact:
            return n
    return None


def cassini_holds(count):
    """Check F(n+1)F(n-1) - F(n)^2 == (-1)^n for 1 <= n < count."""
    f = fib_list(count + 1)
    return all(f[n + 1] * f[n - 1] - f[n] ** 2 == (-1) ** n
               for n in range(1, count))


def main():
    f = fib_list(300)
    print("F(0..12) from the recurrence:", f[:13])
    gf = series_divide([0, 1], [1, -1, -1], 300)
    print("Coefficients of x/(1 - x - x^2) agree for n < 300:", gf == f)
    same = all(fib_matrix(n)[0] == f[n] for n in range(300))
    print("Matrix powers agree for n < 300:", same)
    print("Cassini F(n+1)F(n-1) - F(n)^2 = (-1)^n for 1 <= n < 300:",
          cassini_holds(300))
    value, mults = fib_matrix(1000)
    print(f"F(1000) has {len(str(value))} digits; found with {mults} "
          "matrix products")
    print(f"(n log10(phi) predicts {1000 * math.log10((1 + 5 ** 0.5) / 2):.1f}"
          " digits)")
    n = first_binet_failure(200)
    print(f"Rounded float Binet first fails at n = {n}:")
    print(f"  exact F({n}) = {f[n]}")
    print(f"  float Binet  = {binet_float(n)}")
    print(f"  F({n}) has {len(str(f[n]))} digits. A float carries about 16, and")
    print("  the relative rounding error of phi grows about n-fold in phi^n.")
    print()
    print("Epistemic status: the agreements for n < 300 are exact integer")
    print("computations, i.e. exhaustive checks of finitely many cases; the")
    print("proofs for all n are in the lesson (and in Lean). The Binet failure")
    print("is a fact about 64-bit floating point, not about the formula,")
    print("which is exact in real arithmetic.")


if __name__ == "__main__":
    main()
