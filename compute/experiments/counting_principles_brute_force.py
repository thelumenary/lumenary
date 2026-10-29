"""Counting without listing - and then listing anyway, to check.

Each counting principle predicts a number: the multiplication principle for
PINs and podiums, factorials for arrangements, complementary counting for
"at least one", and the overlap rule for "or". This experiment computes
each prediction from the formula and then lists every possibility with
itertools to count them one by one. It also shows the classic mistake of
adding overlapping cases without subtracting the overlap.
"""

from itertools import permutations, product
from math import factorial

EXPERIMENT = {
    "id": "counting_principles_brute_force",
    "title": "Counting principles checked by listing every case",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["counting-principles"],
    "summary": (
        "Compares formula counts with brute-force enumeration: 4-digit PINs "
        "(10^4), PINs without repeats (10*9*8*7) and with a repeat "
        "(complement), podium finishes (8*7*6), arrangements of 5 letters "
        "(5!), 3-symbol codes with at least one digit (36^3 - 26^3), and "
        "numbers up to 100 divisible by 2 or 5 (50 + 20 - 10). Exhaustive "
        "for these cases; the principles themselves are proved in the lesson."
    ),
    "packages": [],
}

DIGITS = "0123456789"
LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


def ordered_selections(n, k):
    """n * (n - 1) * ... * (n - k + 1), the number of ordered selections."""
    if k > n:
        return 0
    return factorial(n) // factorial(n - k)


def count_pins(repeats_allowed=True):
    """Count 4-digit PINs by listing them (optionally with distinct digits)."""
    pins = product(DIGITS, repeat=4)
    if repeats_allowed:
        return sum(1 for _ in pins)
    return sum(1 for p in pins if len(set(p)) == 4)


def count_codes_with_digit(length):
    """Count codes of `length` symbols (letters or digits) with a digit."""
    symbols = LETTERS + DIGITS
    return sum(1 for code in product(symbols, repeat=length)
               if any(c in DIGITS for c in code))


def count_divisible_by_either(limit, a, b):
    """How many of 1..limit are divisible by a or by b, by listing."""
    return sum(1 for n in range(1, limit + 1) if n % a == 0 or n % b == 0)


def main():
    rows = [
        ("4-digit PINs", 10 ** 4, count_pins()),
        ("PINs, no repeated digit", ordered_selections(10, 4),
         count_pins(repeats_allowed=False)),
        ("PINs, some digit repeated", 10 ** 4 - ordered_selections(10, 4),
         count_pins() - count_pins(repeats_allowed=False)),
        ("podiums: 8 runners", ordered_selections(8, 3),
         sum(1 for _ in permutations(range(8), 3))),
        ("arrangements of LUMEN", factorial(5),
         len(set(permutations("LUMEN")))),
        ("3-symbol codes with a digit", 36 ** 3 - 26 ** 3,
         count_codes_with_digit(3)),
        ("1-100 divisible by 2 or 5", 50 + 20 - 10,
         count_divisible_by_either(100, 2, 5)),
    ]
    print(f"{'what is counted':<30}{'formula':>9}{'listed':>9}  agree?")
    for name, formula, listed in rows:
        print(f"{name:<30}{formula:>9}{listed:>9}  {formula == listed}")
    print()
    print("The overlap mistake: 50 multiples of 2 plus 20 multiples of 5 is")
    print("70, but 10, 20, ..., 100 were counted twice. 70 - 10 = 60.")
    print()
    word = "LETTER"
    print(f"Arrangements of {word} (two Es and two Ts look identical):")
    print(f"  {len(word)}! = {factorial(len(word))} orders of the "
          f"{len(word)} tiles, but only {len(set(permutations(word)))} "
          "different words.")
    print()
    print("Epistemic status: exact counts, exhaustive for the cases listed")
    print("(up to 46,656 codes). Agreement in these cases is evidence; the")
    print("lesson's proofs show the formulas hold for every n and k.")


if __name__ == "__main__":
    main()
