"""Closing in on the square root of 2 with rationals only: cuts and Cauchy sequences.

Two sequences of exact fractions approach the "missing" number sqrt(2): the
Babylonian (Newton) iteration x -> (x + 2/x)/2 from above, and the map
q -> (2q + 2)/(q + 2) from below, which the lesson uses to show that the
Dedekind cut {q : q < 0 or q^2 < 2} has no largest element. The experiment
checks with exact rational arithmetic that the lower terms stay inside the
cut, the upper terms stay outside, the gap between them shrinks, and the two
sequences are equivalent Cauchy sequences (their difference tends to 0). It
also checks that no fraction with denominator up to 1000 squares to 2. All
arithmetic is exact; the statements about limits are not proved by it.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "number_system_constructions_cauchy_sqrt2",
    "title": "Closing in on the square root of 2 with fractions",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["number-system-constructions"],
    "summary": (
        "Runs the Babylonian iteration x -> (x + 2/x)/2 (from above) and the map "
        "q -> (2q + 2)/(q + 2) (from below) in exact fractions, checks that the "
        "lower terms lie in the Dedekind cut of sqrt(2) and the upper ones do not, "
        "and watches the gap shrink: two equivalent Cauchy sequences of rationals "
        "with no rational limit. Finite and exact; limits are left to the proofs."
    ),
    "packages": [],
}

TWO = Fraction(2)


def in_cut(q):
    """Membership in the Dedekind cut of sqrt(2): q < 0 or q^2 < 2."""
    return q < 0 or q * q < TWO


def babylonian(x):
    """One Newton step for x^2 = 2: the average of x and 2/x."""
    return (x + TWO / x) / 2


def climb(q):
    """The lesson's step inside the cut: (2q + 2)/(q + 2) > q when q^2 < 2."""
    return (2 * q + 2) / (q + 2)


def iterate(step, start, n):
    """The list [start, step(start), ..., step^n(start)]."""
    terms = [Fraction(start)]
    for _ in range(n):
        terms.append(step(terms[-1]))
    return terms


def no_rational_root(max_den):
    """True if no p/q with 1 <= q <= max_den has (p/q)^2 = 2."""
    for q in range(1, max_den + 1):
        p = int((2 * q * q) ** 0.5)
        if any(r * r == 2 * q * q for r in (p - 1, p, p + 1)):
            return False
    return True


def main():
    upper = iterate(babylonian, 2, 5)
    lower = iterate(climb, 1, 5)
    print(" n  lower (in cut)   upper (not in cut)  gap upper - lower")
    for n, (lo, up) in enumerate(zip(lower, upper)):
        lo_s, up_s = f"{lo}", f"{up}"
        if len(up_s) > 18:
            up_s = f"({len(str(up.numerator))} digits)/..."
        gap = float(up - lo)
        print(f"{n:>2}  {lo_s:<15}  {up_s:<18}  {gap:.3e}")
    print("all lower terms in the cut:", all(in_cut(q) for q in lower))
    print("no upper term in the cut:  ", not any(in_cut(x) for x in upper))
    print("lower terms increase:      ",
          all(a < b for a, b in zip(lower, lower[1:])))
    err = [float(x * x - TWO) for x in upper]
    print("upper x^2 - 2:", ", ".join(f"{e:.1e}" for e in err[1:]))
    print("(Newton roughly squares the error at each step.)")
    print("no fraction p/q with q <= 1000 squares to 2:", no_rational_root(1000))
    print()
    print("Epistemic status: exact rational arithmetic for finitely many terms.")
    print("It shows the gap shrinking but cannot show that it tends to 0, nor")
    print("that sqrt(2) is irrational (only that no small fraction works). Those")
    print("are proved in the lesson and in the lesson on real numbers.")


if __name__ == "__main__":
    main()
