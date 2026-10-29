"""Catalan numbers: brute force, a recurrence, a generating function, a formula.

We count balanced strings of n pairs of brackets by checking all 4^n strings
of length 2n (feasible for n <= 8), and compare with Segner's recurrence
C(n+1) = sum C(i) C(n-i), with the closed form binom(2n, n)/(n + 1), and with
the generating function C(x), which satisfies C(x) = 1 + x C(x)^2. We find
the coefficients of C(x) by iterating C <- 1 + x C^2 on truncated power
series: each round fixes at least one more coefficient, which is exactly how
formal power series "converge" with no analysis at all. Finally we compare
C(n) with the asymptotic formula 4^n / (sqrt(pi) n^(3/2)).
"""

import itertools
import math

EXPERIMENT = {
    "id": "recurrences_generating_functions_catalan",
    "title": "Catalan numbers four ways, and their growth",
    "evidence": ["exhaustive-finite", "exact", "numerical"],
    "lessons": ["recurrences-generating-functions"],
    "summary": (
        "Counts balanced bracket strings by brute force for n <= 8, and checks "
        "the counts against Segner's recurrence, the formula binom(2n, n)/(n+1) "
        "and the coefficients of the generating function C(x) = 1 + x C(x)^2, "
        "found by fixed-point iteration on truncated power series. Then measures "
        "the ratio of C(n) to 4^n/(sqrt(pi) n^(3/2)) for n up to 1000."
    ),
    "packages": [],
}


def is_balanced(s):
    """True if the string of '(' and ')' is a balanced bracket sequence."""
    depth = 0
    for ch in s:
        depth += 1 if ch == "(" else -1
        if depth < 0:
            return False
    return depth == 0


def brute_force_count(n):
    """Number of balanced strings with n pairs, by checking all 4^n strings."""
    return sum(is_balanced(s) for s in itertools.product("()", repeat=2 * n))


def segner(count):
    """C(0), ..., C(count - 1) from C(0) = 1 and C(n+1) = sum C(i) C(n - i)."""
    c = [1]
    while len(c) < count:
        n = len(c) - 1
        c.append(sum(c[i] * c[n - i] for i in range(n + 1)))
    return c[:count]


def closed_form(n):
    """binom(2n, n) / (n + 1), which is always an integer."""
    q, r = divmod(math.comb(2 * n, n), n + 1)
    if r:
        raise ArithmeticError("binom(2n, n) should be divisible by n + 1")
    return q


def series_fixed_point(count, rounds):
    """Iterate C <- 1 + x*C^2, keeping the first `count` coefficients."""
    c = [0] * count
    for _ in range(rounds):
        square = [sum(c[i] * c[k - i] for i in range(k + 1))
                  for k in range(count)]
        c = [1] + square[: count - 1]
    return c


def asymptotic_ratio(n):
    """C(n) divided by 4^n / (sqrt(pi) n^(3/2)); computed with logarithms."""
    log_c = math.lgamma(2 * n + 1) - 2 * math.lgamma(n + 1) - math.log(n + 1)
    log_a = n * math.log(4) - 0.5 * math.log(math.pi) - 1.5 * math.log(n)
    return math.exp(log_c - log_a)


def main():
    rec = segner(16)
    print(" n  brute force  Segner  binom(2n,n)/(n+1)")
    for n in range(9):
        print(f"{n:2d}  {brute_force_count(n):11d}  {rec[n]:6d}  "
              f"{closed_form(n):17d}")
    ok = all(rec[n] == closed_form(n) for n in range(16))
    print("Segner = closed form for n < 16:", ok)
    for rounds in (3, 6, 16):
        c = series_fixed_point(16, rounds)
        agree = sum(1 for a, b in zip(c, rec) if a == b)
        print(f"{rounds:2d} rounds of C <- 1 + x C^2: {c[:7]}, "
              f"{agree}/16 correct")
    print("C(n) / (4^n / (sqrt(pi) n^1.5)):")
    for n in (10, 100, 1000):
        print(f"  n = {n:4d}: {asymptotic_ratio(n):.5f}")
    print("(the ratio is close to 1 - 9/(8n), so it tends to 1)")
    print()
    print("Epistemic status: the table is an exhaustive check of all strings")
    print("for n <= 8 plus exact integer arithmetic for n < 16; it proves")
    print("nothing about larger n (the reflection proof in the lesson does).")
    print("The ratios are floating-point evidence for the asymptotic formula,")
    print("which is proved with Stirling's formula.")


if __name__ == "__main__":
    main()
