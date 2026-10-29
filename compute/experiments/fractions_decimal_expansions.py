"""Which fractions have decimals that stop?

Long division turns a fraction into a decimal. The remainders can only be
0, 1, ..., b - 1, so either a remainder of 0 appears (the decimal stops) or
a remainder repeats (the digits repeat forever). We print the decimals of
1/2 to 1/20 and then test the rule: a fraction in lowest terms has a decimal
that stops exactly when its denominator is built from 2s and 5s only.
"""

from math import gcd

EXPERIMENT = {
    "id": "fractions_decimal_expansions",
    "title": "Decimals that stop and decimals that repeat",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["fractions"],
    "summary": (
        "Computes decimal expansions by long division, detecting the repeating block "
        "from a repeated remainder, for 1/2 to 1/20. Then checks, for all 4,950 "
        "fractions a/b with 1 <= a < b <= 100, that the decimal stops exactly when the "
        "lowest-terms denominator has no prime factors other than 2 and 5. Complete "
        "for these fractions; the lesson explains why the rule holds in general."
    ),
    "packages": [],
}


def decimal_expansion(a, b):
    """Long division of a/b (b > 0, a >= 0).

    Returns (whole part, digits before the repeat, repeating digits); the
    repeating list is empty when the decimal stops.
    """
    if b <= 0 or a < 0:
        raise ValueError("need a >= 0 and b > 0")
    whole, r = divmod(a, b)
    digits, seen = [], {}
    while r and r not in seen:
        seen[r] = len(digits)
        digit, r = divmod(10 * r, b)
        digits.append(digit)
    if r == 0:
        return whole, digits, []
    start = seen[r]
    return whole, digits[:start], digits[start:]


def show(a, b):
    """The decimal as text, with the repeating block in brackets: 0.1(6)."""
    whole, fixed, repeat = decimal_expansion(a, b)
    text = "".join(map(str, fixed))
    if repeat:
        text += "(" + "".join(map(str, repeat)) + ")"
    return f"{whole}.{text}" if text else str(whole)


def only_twos_and_fives(n):
    """True if n > 0 has no prime factors other than 2 and 5."""
    if n <= 0:
        raise ValueError("n must be positive")
    for p in (2, 5):
        while n % p == 0:
            n //= p
    return n == 1


def check_rule(max_den):
    """Return (fractions checked, rule correct, decimals that stop)."""
    checked = correct = stops = 0
    for b in range(2, max_den + 1):
        for a in range(1, b):
            checked += 1
            terminates = decimal_expansion(a, b)[2] == []
            stops += terminates
            correct += terminates == only_twos_and_fives(b // gcd(a, b))
    return checked, correct, stops


def main():
    print("Long division of 1/b; brackets mark digits that repeat forever:")
    cells = [f"1/{b:<2} = {show(1, b)}" for b in range(2, 21)]
    for i in range(0, len(cells), 2):
        print("  " + "".join(f"{c:<36}" for c in cells[i:i + 2]).rstrip())
    print()
    checked, correct, stops = check_rule(100)
    print(f"All {checked:,} fractions a/b with 1 <= a < b <= 100:")
    print(f"  {stops:,} have decimals that stop; the rest repeat forever.")
    print("  Rule: 'stops exactly when the lowest-terms denominator uses only")
    print(f"  2s and 5s' is right in {correct:,} of {checked:,} cases.")
    print(f"  Careful with lowest terms: 3/12 = {show(3, 12)} stops, because"
          f" 3/12 = 1/4.")
    print()
    print("Epistemic status: long division here is exact (whole-number")
    print("remainders, no rounding), so each expansion is correct; the rule is")
    print("checked completely for these 4,950 fractions only. Why it holds for")
    print("every fraction: a stopping decimal is m/10^k, and the only prime")
    print("factors of 10^k are 2 and 5.")


if __name__ == "__main__":
    main()
