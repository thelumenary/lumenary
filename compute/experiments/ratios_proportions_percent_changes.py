"""Percentage changes multiply: exact arithmetic with fractions.

A rise of p% multiplies an amount by 1 + p/100 and a fall of p% by
1 - p/100. So "up p%, then down p%" multiplies by (1 + p/100)(1 - p/100),
which is 1 - (p/100)**2: always a little less than 1. This experiment
computes these factors exactly with Python's Fraction type, searches for the
pairs of changes where simply adding the percentages happens to work, finds
the fall that undoes a rise (100p/(100 + p) percent), and compares five 10%
rises with one 50% rise.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "ratios_proportions_percent_changes",
    "title": "Percentage changes multiply, they do not add",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["ratios-proportions"],
    "summary": (
        "Computes exact multipliers for successive percentage changes with "
        "fractions: up p% then down p% gives 1 - (p/100)^2; adding two "
        "percentages gives the right answer only when one of them is 0 "
        "(searched for all whole p, q from -99 to 100); a rise of p% is undone "
        "by a fall of 100p/(100 + p)%; five 10% rises give 61.051%, not 50%. "
        "Exact, finite checks of identities the lesson proves in general."
    ),
    "packages": [],
}


def factor(p):
    """The multiplier for a change of p percent (p may be negative)."""
    return 1 + Fraction(p) / 100


def combined(*changes):
    """The single multiplier equivalent to several percentage changes."""
    total = Fraction(1)
    for p in changes:
        total *= factor(p)
    return total


def as_percent_change(multiplier):
    """Turn a multiplier such as 99/100 into a percentage change (-1)."""
    return (Fraction(multiplier) - 1) * 100


def undo_rise(p):
    """The percentage fall that exactly undoes a rise of p percent."""
    p = Fraction(p)
    if p <= -100:
        raise ValueError("a fall of 100% or more cannot be undone")
    return 100 * p / (100 + p)


def when_adding_works(low, high):
    """Whole-number pairs (p, q) in range where adding the percentages works.

    Adding guesses the multiplier 1 + (p + q)/100; the true multiplier is
    (1 + p/100)(1 + q/100) = 1 + (p + q)/100 + pq/10000. Returns the list of
    pairs where the guess is exactly right, and the number of pairs tried.
    """
    hits = []
    tried = 0
    for p in range(low, high + 1):
        for q in range(low, high + 1):
            tried += 1
            if combined(p, q) == factor(p + q):
                hits.append((p, q))
    return hits, tried


def fmt(x):
    """Show a Fraction as a decimal when it is one, else as a fraction."""
    x = Fraction(x)
    if x.denominator == 1:
        return str(x.numerator)
    if all(p in (2, 5) for p in _prime_factors(x.denominator)):
        return f"{float(x):.6f}".rstrip("0")
    return f"{x} (about {float(x):.2f})"


def _prime_factors(n):
    """Prime factors of n > 0 (with repetition)."""
    out, d = [], 2
    while d * d <= n:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def main():
    print("Up p% then down p%: multiplier (1 + p/100)(1 - p/100)")
    print("    p    multiplier    overall change")
    for p in [5, 10, 20, 25, 50, 100]:
        m = combined(p, -p)
        print(f"  {p:3d}%   {fmt(m):>10}    {fmt(as_percent_change(m)):>8}%")
    hits, tried = when_adding_works(-99, 100)
    zero = all(p == 0 or q == 0 for p, q in hits)
    print(f"Adding p% and q% gives the right answer for {len(hits)} of "
          f"{tried} pairs")
    print(f"  (whole p, q in -99..100); every one has p = 0 or q = 0: {zero}")
    print()
    print("The fall that undoes a rise of p%:")
    for p in [10, 25, 50, 100, 300]:
        print(f"  rise {p:3d}%  ->  fall {fmt(undo_rise(p))}%")
    print()
    five = combined(10, 10, 10, 10, 10)
    print(f"Five rises of 10%: multiplier {fmt(five)}, "
          f"a rise of {fmt(as_percent_change(five))}%, not 50%.")
    print()
    print("Epistemic status: exact rational arithmetic. The search is")
    print("exhaustive for 40,000 whole-number pairs only; that adding works")
    print("exactly when pq = 0, for every p and q, follows from the algebra")
    print("(1 + p/100)(1 + q/100) = 1 + (p + q)/100 + pq/10000 in the lesson.")


if __name__ == "__main__":
    main()
