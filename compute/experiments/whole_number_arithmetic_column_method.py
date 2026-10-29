"""The written multiplication method, step by step, checked against Python.

The column method multiplies by one digit at a time, regrouping ("carrying")
ten ones as one ten, then adds the partial products shifted by place value.
The area model splits both numbers by place value and adds the same partial
products in a different grouping. We print the working for 47 x 23, compare
the digit-by-digit method with Python's built-in multiplication on every pair
of numbers below 200 and on random large pairs, and show what goes wrong when
the carries are forgotten.
"""

import random

EXPERIMENT = {
    "id": "whole_number_arithmetic_column_method",
    "title": "The column method for multiplication, step by step",
    "evidence": ["exhaustive-finite", "experimental"],
    "lessons": ["whole-number-arithmetic"],
    "summary": (
        "Implements the written column method digit by digit (with carries) and the "
        "area model, prints the working for 47 x 23, and checks the method against "
        "Python's multiplication for all 40,000 pairs below 200 (a complete check of "
        "those pairs) and 2,000 random large pairs (evidence only). A version that "
        "forgets to carry fails, showing that carrying is regrouping, not a trick."
    ),
    "packages": [],
}


def digits(n):
    """Digits of a whole number, ones first: digits(407) == [7, 0, 4]."""
    if n < 0:
        raise ValueError("whole numbers only")
    out = [n % 10]
    n //= 10
    while n:
        out.append(n % 10)
        n //= 10
    return out


def from_digits(ds):
    """Inverse of digits(): from_digits([7, 0, 4]) == 407."""
    return sum(d * 10 ** k for k, d in enumerate(ds))


def times_one_digit(a, d, carry_on=True):
    """Multiply a by a single digit d as in the column method.

    Returns (product, steps) where each step is (digit, digit*d + carry_in,
    written digit, carry_out). With carry_on=False the carries are dropped,
    which is the classic mistake.
    """
    if not 0 <= d <= 9:
        raise ValueError("d must be a single digit")
    carry, written, steps = 0, [], []
    for x in digits(a):
        total = x * d + carry
        new_carry = total // 10 if carry_on else 0
        written.append(total % 10)
        steps.append((x, total, total % 10, new_carry))
        carry = new_carry
    while carry:
        written.append(carry % 10)
        carry //= 10
    return from_digits(written), steps


def partial_products(a, b, carry_on=True):
    """The rows of the column method: a times each digit of b, shifted."""
    return [times_one_digit(a, d, carry_on)[0] * 10 ** k
            for k, d in enumerate(digits(b))]


def column_multiply(a, b, carry_on=True):
    """Multiply by the written column method."""
    return sum(partial_products(a, b, carry_on))


def area_pieces(a, b):
    """Area model: each non-zero place-value part of a times each part of b."""
    def parts(n):
        return [d * 10 ** k for k, d in enumerate(digits(n)) if d]
    return [(x, y, x * y) for x in parts(a)[::-1] for y in parts(b)[::-1]]


def count_mismatches(pairs, carry_on=True):
    """How many pairs (a, b) the column method gets wrong."""
    return sum(column_multiply(a, b, carry_on) != a * b for a, b in pairs)


def main():
    a, b = 47, 23
    print(f"Column method for {a} x {b}")
    product, steps = times_one_digit(a, 3)
    for x, total, write, carry in steps:
        print(f"  {x} x 3 + carry = {total}: write {write}, carry {carry}")
    rows = partial_products(a, b)
    print(f"  row 1: {a} x 3 = {rows[0]}")
    print(f"  row 2: {a} x 20 = {a} x 2 x 10 = {rows[1]}")
    print(f"  total: {rows[0]} + {rows[1]} = {sum(rows)}")
    pieces = area_pieces(a, b)
    print("Area model: " + ", ".join(f"{x} x {y} = {p}" for x, y, p in pieces))
    print("  " + " + ".join(str(p) for _, _, p in pieces)
          + f" = {sum(p for _, _, p in pieces)} (same pieces, regrouped)")
    print()
    small = [(x, y) for x in range(200) for y in range(200)]
    rng = random.Random(2024)
    big = [(rng.randrange(10 ** 5, 10 ** 6), rng.randrange(10 ** 3, 10 ** 4))
           for _ in range(2000)]
    print("Column method versus Python's built-in multiplication:")
    print(f"  all {len(small):,} pairs below 200: "
          f"{count_mismatches(small)} mismatches")
    print(f"  {len(big):,} random 6-digit x 4-digit pairs: "
          f"{count_mismatches(big)} mismatches")
    wrong = count_mismatches(small, carry_on=False)
    print("A broken method that forgets to carry:")
    print(f"  47 x 3 gives {column_multiply(47, 3, carry_on=False)}, not 141;"
          f" wrong on {wrong:,} of the {len(small):,} pairs")
    print()
    print("Epistemic status: the 40,000 small pairs are checked completely, so the")
    print("method is correct for those; the random pairs are evidence only. Why it")
    print("works for every pair is the lesson's argument: place value plus the")
    print("distributive law.")


if __name__ == "__main__":
    main()
