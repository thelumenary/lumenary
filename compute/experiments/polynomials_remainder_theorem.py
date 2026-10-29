"""Synthetic division, the remainder theorem and the rational root test.

Divides polynomials by x - a with exact rational arithmetic (synthetic
division, i.e. Horner's scheme), checks on thousands of random cases that the
remainder equals p(a), and uses the rational root test to factorise a cubic
completely. The random check is experimental evidence; the lesson's proof of
the remainder theorem covers every polynomial and every number a.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "polynomials_remainder_theorem",
    "title": "Synthetic division and the remainder theorem",
    "evidence": ["exact", "experimental"],
    "lessons": ["polynomials"],
    "summary": (
        "Divides polynomials by x - a with exact fractions (synthetic division), "
        "confirms on 2,000 random cases that the remainder is p(a), and finds all "
        "rational roots of 2x^3 - 3x^2 - 11x + 6 with the rational root test. The "
        "random check is evidence for the cases tried; the lesson's proof covers all."
    ),
    "packages": [],
}


def synthetic_division(coeffs, a):
    """Divide p by (x - a). ``coeffs`` lists p's coefficients, highest first.

    Returns (quotient coefficients, remainder), computed exactly.
    """
    if not coeffs:
        raise ValueError("p must have at least one coefficient")
    running = []
    value = Fraction(0)
    for c in coeffs:
        value = value * a + c
        running.append(value)
    return running[:-1], running[-1]


def evaluate(coeffs, x):
    """p(x) computed term by term (not by Horner), for an independent check."""
    n = len(coeffs) - 1
    return sum(Fraction(c) * Fraction(x) ** (n - i) for i, c in enumerate(coeffs))


def divisors(n):
    """Positive divisors of the non-zero integer n."""
    n = abs(n)
    if n == 0:
        raise ValueError("0 has infinitely many divisors")
    return [d for d in range(1, n + 1) if n % d == 0]


def rational_root_candidates(coeffs):
    """All +-p/q with p | constant term and q | leading coefficient (sorted)."""
    lead, const = coeffs[0], coeffs[-1]
    cands = {s * Fraction(p, q) for p in divisors(const)
             for q in divisors(lead) for s in (1, -1)}
    return sorted(cands)


def rational_roots(coeffs):
    """The candidates of the rational root test that really are roots."""
    return [r for r in rational_root_candidates(coeffs)
            if evaluate(coeffs, r) == 0]


def show(coeffs):
    """Readable form of a polynomial, e.g. 2x^2 + 3x - 2."""
    n = len(coeffs) - 1
    terms = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        k = n - i
        mag = abs(c)
        body = "" if (mag == 1 and k > 0) else str(mag)
        body += "" if k == 0 else ("x" if k == 1 else f"x^{k}")
        terms.append(("- " if c < 0 else "+ ") + body)
    if not terms:
        return "0"
    text = " ".join(terms)
    return text[2:] if text.startswith("+ ") else "-" + text[2:]


def random_check(trials, seed=2024):
    """Compare the synthetic-division remainder with p(a) on random cases.

    Returns the number of disagreements (the theorem predicts 0).
    """
    rng = random.Random(seed)
    failures = 0
    for _ in range(trials):
        coeffs = [rng.randint(-9, 9) for _ in range(rng.randint(1, 7))]
        a = Fraction(rng.randint(-20, 20), rng.randint(1, 6))
        _, remainder = synthetic_division(coeffs, a)
        failures += remainder != evaluate(coeffs, a)
    return failures


def main():
    p = [2, -3, -11, 6]
    print(f"p(x) = {show(p)}")
    q, r = synthetic_division(p, 3)
    print(f"divide by x - 3:  quotient {show(q)},  remainder {r}")
    print(f"p(3) = {evaluate(p, 3)}, so x - 3 is a factor (factor theorem)")
    cands = rational_root_candidates(p)
    print(f"rational root test: {len(cands)} candidates +-p/q,")
    print("  p | 6 and q | 2:", ", ".join(str(c) for c in cands if c > 0))
    roots = rational_roots(p)
    print("  roots found:", ", ".join(str(x) for x in roots))
    print("  so p(x) = (x + 2)(2x - 1)(x - 3)")
    print()
    _, r2 = synthetic_division([1, 0, 0, -2], Fraction(5, 4))
    print(f"x^3 - 2 divided by x - 5/4: remainder {r2} = p(5/4)")
    found = rational_roots([1, 0, 0, -2])
    print(f"x^3 - 2: candidates +-1, +-2; rational roots: {found or 'none'}")
    print("  so the cube root of 2 is irrational")
    trials = 2000
    print(f"random check, {trials} polynomials and points a:"
          f" {random_check(trials)} disagreements")
    print()
    print("Epistemic status: the worked divisions and the root search are exact")
    print("computations with fractions. The random check is experimental evidence")
    print("for 2,000 cases only; the remainder theorem's proof in the lesson is")
    print("what guarantees remainder = p(a) for every polynomial and every a.")


if __name__ == "__main__":
    main()
