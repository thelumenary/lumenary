"""What to do with a 5: three rounding rules and Python's own round().

At school, halves round up (35 -> 40). Python's built-in round() uses another
rule, "round half to even" (25 -> 20, 35 -> 40), which many computers and
scientists use because it has no upward bias. We compare the rules on every
whole number from 0 to 9,999, show Python's round() in action, and show why
round(2.675, 2) gives 2.67: the computer never stored 2.675 exactly.
"""

from decimal import Decimal

EXPERIMENT = {
    "id": "estimation_halfway_rules",
    "title": "Rounding halves: up, to even, or down?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["estimation"],
    "summary": (
        "Rounds every whole number from 0 to 9,999 to the nearest ten with three "
        "rules (halves up, halves to even, always down) and computes each rule's "
        "average error exactly: +0.5, 0 and -4.5. Shows that Python's round() rounds "
        "halves to even, and that round(2.675, 2) = 2.67 because the float stored for "
        "2.675 is slightly smaller than 2.675."
    ),
    "packages": [],
}


def half_up(n):
    """School rounding to the nearest ten: halves go up."""
    return (n + 5) // 10 * 10


def half_even(n):
    """Nearest ten; a half goes to the ten whose tens digit is even."""
    q, r = divmod(n, 10)
    if r > 5 or (r == 5 and q % 2 == 1):
        q += 1
    return q * 10


def always_down(n):
    """Chop off the ones digit (this is not rounding to the nearest ten!)."""
    return n // 10 * 10


RULES = [("halves up (school)", half_up), ("halves to even", half_even),
         ("always down", always_down)]


def average_error(rule, numbers):
    """Exact average of rule(n) - n, as a Decimal."""
    total = sum(rule(n) - n for n in numbers)
    return Decimal(total) / Decimal(len(numbers))


def main():
    numbers = range(10_000)
    print("Rounding 0..9,999 to the nearest ten; average of (rounded - exact):")
    for name, rule in RULES:
        print(f"  {name:<20} {average_error(rule, numbers):+.1f}")
    print("  Halves-up pushes totals up a little; halves-to-even does not.")
    print()
    print("Halves up and halves to even can differ only on numbers ending in 5:")
    for n in (25, 35, 45, 65):
        print(f"  {n:>5}: up -> {half_up(n):>5}, to even -> {half_even(n):>5}")
    print()
    print("Python's built-in round() rounds halves to even:")
    print(f"  round(2.5) = {round(2.5)}, round(3.5) = {round(3.5)},"
          f" round(25, -1) = {round(25, -1)}, round(35, -1) = {round(35, -1)}")
    agree = all(round(n, -1) == half_even(n) for n in numbers)
    print(f"  round(n, -1) == halves-to-even for all n in 0..9,999: {agree}")
    print()
    print(f"A float surprise: round(2.675, 2) = {round(2.675, 2)}, because the")
    print("number the computer actually stores for 2.675 is")
    print(f"  {Decimal(2.675)}")
    print()
    print("Epistemic status: all averages are exact (every number was checked")
    print("and the arithmetic uses whole numbers and Decimal). Which rule is")
    print("'right' is a choice, not a theorem: each rule is a convention.")


if __name__ == "__main__":
    main()
