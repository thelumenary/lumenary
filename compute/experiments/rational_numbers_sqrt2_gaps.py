"""Rationals crowd around the square root of 2, but none of them lands on it.

Three exact computations with fractions:

1. A search of every fraction p/q with 1 <= q <= 2000 for p*p == 2*q*q.
   (It finds none; for each q only p near q * 1.414 needs checking.)
2. Squeezing: halve an interval [lo, hi] with lo*lo < 2 < hi*hi again and
   again. The rational endpoints get as close as we like to each other, yet
   neither square is ever exactly 2.
3. The fractions 1/1, 3/2, 7/5, 17/12, 41/29, ... (each p/q followed by
   (p + 2q)/(p + q)) satisfy p*p - 2*q*q = +1 or -1, so their squares miss 2
   by exactly 1/q**2: astonishingly close, never equal.
"""

from fractions import Fraction
from math import isqrt

EXPERIMENT = {
    "id": "rational_numbers_sqrt2_gaps",
    "title": "Rationals squeeze the square root of 2 but never hit it",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["rational-numbers"],
    "summary": (
        "Searches every fraction with denominator up to 2000 for one whose "
        "square is exactly 2 (none exists), squeezes the square root of 2 "
        "between rational endpoints by repeated halving, and lists fractions "
        "p/q with p*p - 2*q*q = +-1 whose squares miss 2 by exactly 1/q**2. "
        "Exact arithmetic; finite evidence only - the proof is in the lesson."
    ),
    "packages": [],
}


def square_root_two_search(max_q):
    """All (p, q) with 1 <= q <= max_q and p*p == 2*q*q (expected: none).

    For each q, the only candidate is p = isqrt(2*q*q), the largest whole
    number whose square is at most 2*q*q.
    """
    hits = []
    for q in range(1, max_q + 1):
        p = isqrt(2 * q * q)
        if p * p == 2 * q * q:
            hits.append((p, q))
    return hits


def squeeze(steps):
    """Halve [1, 2] ``steps`` times, keeping lo*lo < 2 < hi*hi."""
    lo, hi = Fraction(1), Fraction(2)
    history = [(lo, hi)]
    for _ in range(steps):
        mid = (lo + hi) / 2
        if mid * mid == 2:
            raise AssertionError("found a rational square root of 2")
        if mid * mid < 2:
            lo = mid
        else:
            hi = mid
        history.append((lo, hi))
    return history


def pell_fractions(count):
    """The fractions p/q = 1/1, 3/2, 7/5, ... with p*p - 2*q*q = +-1."""
    p, q = 1, 1
    out = []
    for _ in range(count):
        out.append((p, q))
        p, q = p + 2 * q, p + q
    return out


def main():
    hits = square_root_two_search(2000)
    print("1. Fractions p/q with q <= 2000 and (p/q)^2 = 2:", len(hits))
    print()
    print("2. Squeezing between rationals (lo^2 < 2 < hi^2):")
    for k, (lo, hi) in enumerate(squeeze(10)):
        if k % 2 == 0:
            print(f"   step {k:2d}: {str(lo):>9} < sqrt 2 < {str(hi):<9}"
                  f" width {hi - lo}")
    print()
    print("3. p/q with p^2 - 2q^2 = +-1: the square misses 2 by 1/q^2")
    print("      p/q        p^2 - 2q^2   (p/q)^2 - 2")
    for p, q in pell_fractions(8):
        miss = Fraction(p * p, q * q) - 2
        print(f"   {p:>5}/{q:<6}  {p * p - 2 * q * q:>8}      {miss}")
    print()
    print("Epistemic status: exact, exhaustive for denominators up to 2000;")
    print("the squeeze and the list show rationals getting ever closer to")
    print("sqrt 2. No computation can show that no fraction ever works: that")
    print("needs the proof by contradiction in the lesson.")


if __name__ == "__main__":
    main()
