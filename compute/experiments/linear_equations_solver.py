"""Solving linear equations exactly, and testing the rules for inequalities.

Part 1 solves every equation a*x + b = c*x + d from the lesson exactly, with
Python's Fraction type, by reducing it to the standard form (a - c)x = d - b,
and checks each answer by substituting it back. Part 2 counts, over ALL
equations with small integer coefficients, how many test values satisfy
each one: always 0, 1 or all of them, never exactly 2 - as the lesson's
theorem predicts. Part 3 tests the rule "multiplying an inequality by a
negative number reverses it" on random fractions, and compares the right
and the wrong ("forgot to flip") answers to 7 - 3x <= 19.
"""

import random
from fractions import Fraction as F

EXPERIMENT = {
    "id": "linear_equations_solver",
    "title": "Linear equations: exact solutions and inequality flips",
    "evidence": ["exact", "exhaustive-finite", "experimental"],
    "lessons": ["linear-equations"],
    "summary": (
        "Solves the lesson's equations a*x + b = c*x + d exactly with fractions "
        "via the standard form (a - c)x = d - b and checks each answer by "
        "substitution; counts, for all 2401 equations with coefficients in "
        "-3..3, how many of the values -5..5 solve each one (never exactly two); "
        "and tests the inequality-reversal rule on 10,000 random fractions."
    ),
    "packages": [],
}

#: (description, a, b, c, d) meaning a*x + b = c*x + d.
LESSON_EQUATIONS = [
    ("3x + 1 = x + 9", 3, 1, 1, 9),
    ("500 - 20t = 100 + 30t", -20, 500, 30, 100),
    ("x/3 + 1/2 = (x - 1)/4", F(1, 3), F(1, 2), F(1, 4), F(-1, 4)),
    ("5 - 2x = 11", -2, 5, 0, 11),
    ("2(x + 3) = 2x + 5", 2, 6, 2, 5),
    ("3(x - 2) + x = 4x - 6", 4, -6, 4, -6),
]


def solve_linear(a, b, c, d):
    """Solve a*x + b = c*x + d exactly.

    Returns ("one", x), ("none", None) or ("all", None), following the
    standard form (a - c) x = d - b.
    """
    coeff, rhs = F(a) - F(c), F(d) - F(b)
    if coeff != 0:
        return "one", rhs / coeff
    if rhs != 0:
        return "none", None
    return "all", None


def satisfies(a, b, c, d, x):
    """Does x satisfy a*x + b = c*x + d (exact arithmetic)?"""
    return F(a) * x + b == F(c) * x + d


def solution_counts(coeffs, values):
    """For every (a, b, c, d) with entries in coeffs, count solutions in values.

    Returns a dict {number of solving values: number of equations}.
    """
    counts = {}
    for a in coeffs:
        for b in coeffs:
            for c in coeffs:
                for d in coeffs:
                    k = sum(1 for x in values if satisfies(a, b, c, d, x))
                    counts[k] = counts.get(k, 0) + 1
    return counts


def flip_trials(trials, seed=2024):
    """Random p < q and c < 0 (fractions). Count how often c*q < c*p holds."""
    rng = random.Random(seed)
    flipped = 0
    for _ in range(trials):
        p, q = sorted(F(rng.randint(-99, 99), rng.randint(1, 9)) for _ in "pq")
        if p == q:
            q += 1
        c = -F(rng.randint(1, 99), rng.randint(1, 9))
        flipped += c * q < c * p
    return flipped


def inequality_table(values):
    """Values x with 7 - 3x <= 19, and the two candidate answers."""
    true_set = [x for x in values if 7 - 3 * x <= 19]
    right = [x for x in values if x >= -4]
    wrong = [x for x in values if x <= -4]
    return true_set, right, wrong


def main():
    print("1. Exact solutions via the standard form (a - c)x = d - b")
    for text, a, b, c, d in LESSON_EQUATIONS:
        kind, x = solve_linear(a, b, c, d)
        if kind == "one":
            ok = "checks" if satisfies(a, b, c, d, x) else "FAILS"
            result = f"solution {x}   (substituting back: {ok})"
        elif kind == "none":
            result = "no solution: reduces to 0x = " + str(F(d) - F(b))
        else:
            result = "every number is a solution: 0x = 0"
        print(f"   {text:<24} {result}")
    print()
    values = range(-5, 6)
    counts = solution_counts(range(-3, 4), values)
    print("2. All 2401 equations ax + b = cx + d with a, b, c, d in -3..3:")
    print("   how many of the 11 values -5..5 solve each equation?")
    for k in sorted(counts):
        print(f"   {k:>2} solving value(s): {counts[k]:>4} equations")
    print("   Never 2 to 10: two solutions force every number to be one.")
    print()
    trials = 10_000
    flipped = flip_trials(trials)
    print(f"3. {trials} random fractions p < q and c < 0:")
    print(f"   c*q < c*p (reversed) in {flipped} cases;"
          f" c*p < c*q in {trials - flipped}.")
    true_set, right, wrong = inequality_table(range(-8, 3))
    print("   7 - 3x <= 19 for x in -8..2 is true at", true_set)
    print("   answer x >= -4 picks", right)
    print("   answer x <= -4 (forgot to flip) picks", wrong)
    print()
    print("Epistemic status: part 1 is exact rational arithmetic, and each")
    print("answer is checked by substitution. Part 2 is an exhaustive check of")
    print("2401 equations on 11 values - finite evidence for the lesson's theorem,")
    print("which proves it for all equations and all numbers. Part 3 is a random")
    print("experiment; only the proof shows the reversal rule always holds.")


if __name__ == "__main__":
    main()
