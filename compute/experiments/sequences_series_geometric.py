"""Geometric series in exact arithmetic: 1 + 1/2 + 1/4 + ... and 0.999...

With fractions the partial sums S_n = a(1 - r^n)/(1 - r) are computed with no
rounding, so we can watch the gap a/(1 - r) - S_n = a r^n/(1 - r) shrink
exactly: for 1 + 1/2 + 1/4 + ... the gap after n terms is 1/2^(n-1), and for
0.9 + 0.09 + 0.009 + ... it is 1/10^n. For |r| >= 1 the partial sums
oscillate or grow instead, and the terms do not tend to 0.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "sequences_series_geometric",
    "title": "Geometric series: exact partial sums and gaps",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["sequences-series"],
    "summary": (
        "Computes partial sums of geometric series in exact rational arithmetic, "
        "checks the closed form a(1 - r^n)/(1 - r) for many n, and shows the gap "
        "to a/(1 - r) shrinking exactly (1/2^(n-1) for the halves, 1/10^n for "
        "0.999...). For r = 1, -1 and 2 the partial sums do not settle. The "
        "limit itself is proved in the lesson, not here."
    ),
    "packages": [],
}


def partial_sums(a, r, n):
    """[S_1, ..., S_n] for a + ar + ar^2 + ..., exact for Fractions."""
    if n < 0:
        raise ValueError("n must be non-negative")
    sums, total, term = [], 0 * a, a
    for _ in range(n):
        total += term
        sums.append(total)
        term *= r
    return sums


def closed_form(a, r, n):
    """a(1 - r^n)/(1 - r) for r != 1; n * a when r = 1."""
    if r == 1:
        return n * a
    return a * (1 - r ** n) / (1 - r)


def gap(a, r, n):
    """a/(1 - r) - S_n, the part of the infinite sum still missing."""
    return a / (1 - r) - closed_form(a, r, n)


def terms_needed(a, r, eps):
    """Smallest n with |a/(1 - r) - S_n| < eps (requires |r| < 1)."""
    if not abs(r) < 1:
        raise ValueError("needs |r| < 1")
    n = 0
    while abs(gap(a, r, n)) >= eps:
        n += 1
    return n


def main():
    half, tenth = Fraction(1, 2), Fraction(1, 10)
    print("1 + 1/2 + 1/4 + ...  (a = 1, r = 1/2, limit 2)")
    for n, s in enumerate(partial_sums(Fraction(1), half, 8), start=1):
        print(f"  S_{n} = {str(s):>7}   gap = {str(2 - s)}")
    print()
    print("0.9 + 0.09 + 0.009 + ...  (a = 9/10, r = 1/10, limit 1)")
    for n, s in enumerate(partial_sums(Fraction(9, 10), tenth, 5), start=1):
        print(f"  S_{n} = {float(s):.{n}f}   gap = 1 - S_{n} = {1 - s}")
    print("The gap 1/10^n eventually drops below any positive number, so the")
    print("limit of the partial sums, which is what 0.999... means, is exactly 1.")
    print()
    ok = all(
        partial_sums(Fraction(3), r, 30)[-1] == closed_form(Fraction(3), r, 30)
        for r in (half, -half, Fraction(2, 3), Fraction(-9, 10), Fraction(5))
    )
    print(f"Closed form a(1 - r^n)/(1 - r) agrees with term-by-term sums: {ok}")
    need = terms_needed(Fraction(1), half, Fraction(1, 10 ** 6))
    print(f"Terms of 1 + 1/2 + ... needed to come within 10^-6 of 2: {need}")
    print()
    for r in (1, -1, 2):
        sums = partial_sums(1, r, 8)
        print(f"r = {r:2d}: partial sums {sums} - no limit")
    print()
    print("Epistemic status: exact rational arithmetic for finitely many n;")
    print("the closed form and the limits are proved in the lesson (and in")
    print("Lean); a table of partial sums can only illustrate convergence.")


if __name__ == "__main__":
    main()
