"""Long division by hand, done by machine: why decimals of fractions repeat.

Dividing a by b, each step leaves a remainder 0, 1, ..., b - 1. As soon as a
remainder comes back, the digits after it repeat for ever. This experiment
runs long division with exact integers, records the remainders, and reports
where the repeating block starts and how long it is. It then checks, for
every fraction a/b with 0 <= a < b <= 200, two facts proved in the lesson:
the period is at most b - 1, and the expansion terminates exactly when b (in
lowest terms) has no prime factors other than 2 and 5. Finally it turns every
expansion back into a fraction. All arithmetic is exact (no floating point).
"""

from fractions import Fraction
from math import gcd

EXPERIMENT = {
    "id": "rational_numbers_decimals",
    "title": "Long division: why the decimals of a fraction repeat",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["rational-numbers"],
    "summary": (
        "Runs long division with exact integers, tracking remainders to find "
        "the repeating block of a/b. Checks every fraction with denominator up "
        "to 200: the period never exceeds b - 1, terminating decimals are "
        "exactly those whose reduced denominator is built from 2s and 5s, and "
        "every expansion converts back to the original fraction. Finite "
        "evidence; the lesson's pigeonhole proof covers all fractions."
    ),
    "packages": [],
}


def long_division(a, b):
    """Digits of a/b after the point, for 0 <= a and b > 0.

    Returns (whole, digits, start, period): a/b = whole + 0.d1 d2 d3 ...,
    the digits from index ``start`` on repeat with length ``period``.
    A terminating decimal has repeating block "0" (period 1, digit 0).
    """
    if b <= 0 or a < 0:
        raise ValueError("need a >= 0 and b > 0")
    whole, r = divmod(a, b)
    seen = {}
    digits = []
    while r not in seen:
        seen[r] = len(digits)
        digit, r = divmod(10 * r, b)
        digits.append(digit)
    start = seen[r]
    return whole, digits, start, len(digits) - start


def decimal_string(a, b):
    """The expansion of a/b with the repeating block in brackets: 0.1(6)."""
    whole, digits, start, period = long_division(a, b)
    pre, block = digits[:start], digits[start:]
    if block == [0]:
        text = "".join(map(str, pre))
        return f"{whole}.{text}" if text else f"{whole}"
    pre_text = "".join(map(str, pre))
    return f"{whole}.{pre_text}({''.join(map(str, block))})"


def only_twos_and_fives(n):
    """True if n > 0 has no prime factor other than 2 and 5."""
    for p in (2, 5):
        while n % p == 0:
            n //= p
    return n == 1


def to_fraction(whole, pre, block):
    """Exact value of whole.pre(block) where pre, block are digit strings.

    x = whole + 0.pre(block); shifting by the block length k and
    subtracting removes the infinite tail: (10**k - 1) * 10**m * x is an
    integer, where m = len(pre).
    """
    m, k = len(pre), len(block)
    head = int(pre) if pre else 0
    if k == 0:
        return whole + Fraction(head, 10 ** m)
    tail = Fraction(int(block), 10 ** k - 1)
    return whole + (head + tail) / 10 ** m


def check_all(max_b):
    """Check the period bound, the 2-and-5 rule and round trips."""
    cases = bad_period = bad_rule = bad_trip = 0
    for b in range(1, max_b + 1):
        for a in range(b):
            whole, digits, start, period = long_division(a, b)
            cases += 1
            terminates = digits[start:] == [0]
            if not terminates and period > b - 1:
                bad_period += 1
            if terminates != only_twos_and_fives(b // gcd(a, b)):
                bad_rule += 1
            pre = "".join(map(str, digits[:start]))
            block = "".join(map(str, digits[start:]))
            if to_fraction(whole, pre, block) != Fraction(a, b):
                bad_trip += 1
    return cases, bad_period, bad_rule, bad_trip


def main():
    print("1/b by long division (repeating block in brackets)")
    print(" b   decimal                 period  only 2s and 5s?")
    for b in range(2, 18):
        _, digits, start, period = long_division(1, b)
        terminates = digits[start:] == [0]
        per = "-" if terminates else str(period)
        rule = "yes" if only_twos_and_fives(b) else "no"
        print(f"{b:2d}   {decimal_string(1, b):<22}  {per:>6}  {rule}")
    print()
    cases, bad_period, bad_rule, bad_trip = check_all(200)
    print(f"All a/b with 0 <= a < b <= 200: {cases} fractions checked.")
    print(f"  period longer than b - 1:                 {bad_period} cases")
    print(f"  2-and-5 rule wrong (either direction):     {bad_rule} cases")
    print(f"  expansion does not convert back exactly:  {bad_trip} cases")
    print(f"0.(27) = {to_fraction(0, '', '27')}   0.1(6) = "
          f"{to_fraction(0, '1', '6')}   0.(9) = {to_fraction(0, '', '9')}")
    print()
    print("Epistemic status: exact integer arithmetic, exhaustive for the")
    print("20,100 fractions listed. It shows remainders repeating; it does not")
    print("prove that every fraction behaves this way. The lesson's proof does:")
    print("only b remainders exist, so one must repeat (pigeonhole).")


if __name__ == "__main__":
    main()
