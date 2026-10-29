"""How often does a quadratic have real roots? The discriminant decides.

Part 1 classifies every quadratic ax^2 + bx + c with whole-number
coefficients from -5 to 5 (a != 0) by the sign of b^2 - 4ac, and checks with
exact fractions that the quadratic formula really gives roots whenever the
discriminant is a perfect square. Part 2 picks coefficients at random from the
interval [-1, 1] and compares the proportion with real roots against the
known exact value (41 + 6 ln 2)/72.
"""

import math
import random
from fractions import Fraction

EXPERIMENT = {
    "id": "quadratics_discriminant",
    "title": "How often does a quadratic have real roots?",
    "evidence": ["exhaustive-finite", "exact", "statistical"],
    "lessons": ["quadratics"],
    "summary": (
        "Classifies all 1,210 quadratics with integer coefficients from -5 to 5 "
        "by the sign of the discriminant and checks the quadratic formula exactly "
        "whenever the roots are rational; then estimates by simulation how often "
        "a quadratic with random coefficients in [-1, 1] has real roots, compared "
        "with the exact value (41 + 6 ln 2)/72."
    ),
    "packages": [],
}


def discriminant(a, b, c):
    """b^2 - 4ac."""
    return b * b - 4 * a * c


def classify(a, b, c):
    """'two', 'one' or 'none': the number of distinct real roots (a != 0)."""
    if a == 0:
        raise ValueError("not a quadratic: a = 0")
    d = discriminant(a, b, c)
    return "two" if d > 0 else ("one" if d == 0 else "none")


def rational_roots(a, b, c):
    """Exact roots by the formula when b^2 - 4ac is a perfect square, else None."""
    d = discriminant(a, b, c)
    if d < 0 or math.isqrt(d) ** 2 != d:
        return None
    s = math.isqrt(d)
    return sorted({Fraction(-b + s, 2 * a), Fraction(-b - s, 2 * a)})


def census(limit=5):
    """Counts of each case over all integer a, b, c in [-limit, limit], a != 0,
    plus how many have rational roots and how many formula checks failed."""
    counts = {"two": 0, "one": 0, "none": 0, "rational": 0, "failures": 0}
    values = range(-limit, limit + 1)
    for a in values:
        if a == 0:
            continue
        for b in values:
            for c in values:
                counts[classify(a, b, c)] += 1
                roots = rational_roots(a, b, c)
                if roots is not None:
                    counts["rational"] += 1
                    counts["failures"] += any(
                        a * x * x + b * x + c != 0 for x in roots)
    return counts


def simulate(trials, seed=2024):
    """Proportion of random quadratics (a, b, c uniform in [-1, 1]) with
    b^2 - 4ac >= 0."""
    rng = random.Random(seed)
    hits = 0
    for _ in range(trials):
        a, b, c = (rng.uniform(-1, 1) for _ in range(3))
        hits += discriminant(a, b, c) >= 0
    return hits / trials


EXACT_PROBABILITY = (41 + 6 * math.log(2)) / 72


def main():
    counts = census()
    total = counts["two"] + counts["one"] + counts["none"]
    print(f"all {total} quadratics with a, b, c in -5..5 and a != 0:")
    print(f"  discriminant > 0 (two real roots): {counts['two']:4d}")
    print(f"  discriminant = 0 (one real root):  {counts['one']:4d}")
    print(f"  discriminant < 0 (no real roots):  {counts['none']:4d}")
    print(f"  perfect-square discriminant (rational roots): {counts['rational']}")
    print(f"  exact checks of the formula's roots that failed: "
          f"{counts['failures']}")
    print()
    trials = 20000
    p = simulate(trials)
    se = math.sqrt(p * (1 - p) / trials)
    print(f"random a, b, c in [-1, 1], {trials} trials:")
    print(f"  proportion with real roots  {p:.4f}  (standard error {se:.4f})")
    print(f"  exact value (41 + 6 ln 2)/72 = {EXACT_PROBABILITY:.4f}")
    print("  Half the time a and c have opposite signs, so -4ac > 0 and the")
    print("  roots are real for sure; that alone gives at least 1/2.")
    print()
    print("Epistemic status: part 1 is an exhaustive, exact check of 1,210")
    print("cases; it illustrates but does not replace the lesson's proof.")
    print("Part 2 is statistical evidence: the simulated proportion should lie")
    print("within about two standard errors of the exact value, which comes from")
    print("an integral we do not compute here.")


if __name__ == "__main__":
    main()
