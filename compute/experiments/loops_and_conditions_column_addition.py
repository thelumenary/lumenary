"""Column addition as a loop with a carry.

The written method for adding whole numbers is a loop over the columns,
from the ones column leftwards: add the two digits and the carry, write
down the ones digit of the total, and carry the tens into the next column.
The program shows every pass of the loop for 368 + 275, then checks the
method against ordinary addition for every pair of numbers below 200 and
for 2000 random pairs of numbers with up to 12 digits, recording the
largest column total and the largest carry ever seen.
"""

import random
import textwrap

EXPERIMENT = {
    "id": "loops_and_conditions_column_addition",
    "title": "Column addition: a loop with a carry",
    "evidence": ["exact", "exhaustive-finite", "experimental"],
    "lessons": ["loops-and-conditions"],
    "summary": (
        "Runs the column-addition loop step by step for 368 + 275, then "
        "compares it with ordinary addition for all 40000 pairs of numbers "
        "below 200 and 2000 seeded random pairs with up to 12 digits. Every "
        "answer agrees, no column total exceeds 19 and no carry exceeds 1. "
        "Exhaustive for small numbers; a sample for large ones."
    ),
    "packages": [],
}

PLACES = ["ones", "tens", "hundreds", "thousands"]


def digits_ones_first(n):
    """The digits of n, ones digit first: 368 -> [8, 6, 3]."""
    out = []
    while n > 0:
        out.append(n % 10)
        n //= 10
    return out


def column_add(a, b):
    """Column addition of a and b.

    Returns (answer, steps); each step is (top, bottom, carry_in, total,
    written, carry_out), one per pass of the loop."""
    top, bottom = digits_ones_first(a), digits_ones_first(b)
    columns = max(len(top), len(bottom))
    carry, written, steps = 0, [], []
    for i in range(columns):
        t = top[i] if i < len(top) else 0
        u = bottom[i] if i < len(bottom) else 0
        total = t + u + carry
        if total >= 10:
            digit, new_carry = total - 10, 1
        else:
            digit, new_carry = total, 0
        steps.append((t, u, carry, total, digit, new_carry))
        written.append(digit)
        carry = new_carry
    if carry:
        written.append(carry)
    answer = sum(d * 10 ** i for i, d in enumerate(written))
    return answer, steps


def check_pairs(pairs):
    """(all answers right?, largest column total, largest carry) for pairs."""
    right, top_total, top_carry = True, 0, 0
    for a, b in pairs:
        answer, steps = column_add(a, b)
        right = right and answer == a + b
        for step in steps:
            top_total = max(top_total, step[3])
            top_carry = max(top_carry, step[5])
    return right, top_total, top_carry


def main():
    answer, steps = column_add(368, 275)
    print("368 + 275, one pass of the loop per column:")
    for place, (t, u, c, total, digit, carry) in zip(PLACES, steps):
        print(f"  {place:<9} {t} + {u} + carry {c} = {total:>2}"
              f"  -> write {digit}, carry {carry}")
    print(f"  answer: {answer}")
    print()
    small = [(a, b) for a in range(200) for b in range(200)]
    rng = random.Random(2024)
    big = [(rng.randrange(10 ** 12), rng.randrange(10 ** 12))
           for _ in range(2000)]
    for label, pairs in [("all pairs below 200", small),
                         ("2000 random pairs, up to 12 digits", big)]:
        right, total, carry = check_pairs(pairs)
        print(f"Checking {label}:")
        print(f"  every answer right: {right}; largest column total: {total};"
              f" largest carry: {carry}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact arithmetic. Exhaustive for the 40000 pairs "
        "of numbers below 200; for big numbers only a seeded random sample "
        "of 2000 pairs was checked, which is evidence, not proof. The "
        "lesson's place-value argument, and the Lean proof, show that the "
        "method is right for every pair and that the carry is never more "
        "than 1 (because 9 + 9 + 1 = 19).",
        width=78,
    ))


if __name__ == "__main__":
    main()
