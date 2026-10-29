"""Division with remainder: one quotient and one remainder, found by search.

For a = q x b + r there are many pairs (q, r) if r may be as large as we like,
but exactly one with 0 <= r < b. We find the answer for 347 eggs in trays of 30
by repeated subtraction, list every pair that would work without the rule
r < b, and then search exhaustively: for every a up to 500 and b from 1 to 12
there is exactly one pair with r < b, and it agrees with Python's divmod.
Finally we see that "5 divided by 0" has no candidate answer at all.
"""

EXPERIMENT = {
    "id": "whole_number_arithmetic_remainders",
    "title": "Exactly one quotient and remainder",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["whole-number-arithmetic"],
    "summary": (
        "Divides by repeated subtraction, lists all pairs (q, r) with a = q x b + r, "
        "and checks by exhaustive search that for every a <= 500 and 1 <= b <= 12 "
        "exactly one pair has 0 <= r < b, agreeing with divmod. This is a complete "
        "check of those 6,012 cases only; the lesson proves it for all numbers."
    ),
    "packages": [],
}


def repeated_subtraction(a, b):
    """Take b away from a as often as possible; return (quotient, remainder)."""
    if b <= 0:
        raise ValueError("b must be positive")
    if a < 0:
        raise ValueError("a must be a whole number")
    q = 0
    while a >= b:
        a -= b
        q += 1
    return q, a


def all_pairs(a, b, small_remainder=True):
    """Every (q, r) of whole numbers with q*b + r == a (and r < b if asked)."""
    if b <= 0:
        raise ValueError("b must be positive")
    pairs = []
    for q in range(a // b + 1):
        r = a - q * b
        if r >= 0 and (r < b or not small_remainder):
            pairs.append((q, r))
    return pairs


def exhaustive_check(max_a, max_b):
    """Return (cases, all unique?, all agree with divmod?)."""
    cases, unique, agree = 0, True, True
    for a in range(max_a + 1):
        for b in range(1, max_b + 1):
            cases += 1
            pairs = all_pairs(a, b)
            unique = unique and len(pairs) == 1
            agree = agree and pairs == [divmod(a, b)]
    return cases, unique, agree


def solutions_of_times_zero(target, search_up_to):
    """All q in 0..search_up_to with q * 0 == target."""
    return [q for q in range(search_up_to + 1) if q * 0 == target]


def main():
    q, r = repeated_subtraction(347, 30)
    print(f"347 eggs, trays of 30: take away 30 a total of {q} times,"
          f" {r} eggs left.")
    print(f"  347 = {q} x 30 + {r}, and {r} < 30")
    loose = all_pairs(347, 30, small_remainder=False)
    shown = ", ".join(f"({a}, {b})" for a, b in loose[:4])
    print(f"Without the rule r < 30 there are {len(loose)} pairs (q, r):")
    print(f"  {shown}, ..., {loose[-1]}")
    print(f"With the rule r < 30 there is only {all_pairs(347, 30)}")
    print()
    cases, unique, agree = exhaustive_check(500, 12)
    print(f"Every a from 0 to 500 and b from 1 to 12 ({cases:,} cases):")
    print(f"  exactly one pair with r < b every time: {unique}")
    print(f"  that pair is Python's divmod(a, b) every time: {agree}")
    print()
    print("Dividing by zero: q x 0 = 5 for q in 0..1000? "
          f"{len(solutions_of_times_zero(5, 1000))} solutions.")
    print("  q x 0 = 0 for q in 0..1000? "
          f"{len(solutions_of_times_zero(0, 1000))} solutions: every q works.")
    print()
    print("Epistemic status: the search is complete for the 6,012 cases it")
    print("checks, so uniqueness is certain there and nowhere else. The lesson's")
    print("argument (multiples of b are b apart) proves it for every a and b > 0.")
    print("The zero search is evidence; q x 0 = 0 for every q is the proof.")


if __name__ == "__main__":
    main()
