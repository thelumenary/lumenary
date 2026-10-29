"""Diagonal arguments, run on finite examples.

1. Cantor's theorem for a 3-element set A: there are 8^3 = 512 functions
   f : A -> P(A). For each one we form the diagonal set D = {a : a not in f(a)}
   and check that D is not a value of f, so no f is onto.
2. The decimal diagonal: for a list of ten numbers in [0, 1) we build a number
   whose n-th digit is 5, or 4 if the n-th number has a 5 there. It differs
   from the n-th number in the n-th digit, and its digits avoid 0 and 9.
3. Why avoid 0 and 9: the naive rule "replace digit x by 9 - x" applied to a
   cleverly chosen list produces 0.4999..., which is the same number as 0.5 -
   the first number on the list.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "countability_diagonal",
    "title": "Diagonal arguments on finite lists",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["countability"],
    "summary": (
        "Checks all 512 functions from a 3-element set to its power set and finds "
        "the diagonal set missing from every image; builds the decimal diagonal "
        "(digits 4 and 5 only) for a list of ten numbers; and shows that a naive "
        "digit rule can output 0.4999... = 0.5, a number already on the list. "
        "Finite illustrations of the general proofs in the lesson."
    ),
    "packages": [],
}


def subsets(elements):
    """All subsets of a finite collection, as frozensets."""
    elements = list(elements)
    return [frozenset(x for x, keep in zip(elements, mask) if keep)
            for mask in product([False, True], repeat=len(elements))]


def diagonal_set(f, domain):
    """Cantor's diagonal set {a in domain : a not in f(a)}."""
    return frozenset(a for a in domain if a not in f[a])


def check_cantor(n):
    """For A = {0, ..., n-1}, return (number of functions A -> P(A),
    number whose image misses the diagonal set, number that are onto)."""
    domain = list(range(n))
    power = subsets(domain)
    total = missed = onto = 0
    for values in product(power, repeat=n):
        f = dict(zip(domain, values))
        total += 1
        missed += diagonal_set(f, domain) not in values
        onto += set(values) == set(power)
    return total, missed, onto


def digits(x, k):
    """The first k digits after the point of x in [0, 1), from the expansion
    that does not end in repeating 9s. x is a Fraction or a Decimal."""
    out = []
    for _ in range(k):
        x *= 10
        d = int(x)                     # floor, as x >= 0
        out.append(d)
        x -= d
    return out


def diagonal_digits(rows):
    """Digit n is 5, or 4 when rows[n][n] == 5."""
    return [4 if row[n] == 5 else 5 for n, row in enumerate(rows)]


def numbers():
    """Ten labelled numbers in [0, 1)."""
    getcontext().prec = 50
    two, three, five = Decimal(2), Decimal(3), Decimal(5)
    return [("1/7", Fraction(1, 7)), ("1/2", Fraction(1, 2)),
            ("2/3", Fraction(2, 3)), ("5/11", Fraction(5, 11)),
            ("sqrt2 - 1", two.sqrt() - 1), ("sqrt3 - 1", three.sqrt() - 1),
            ("(sqrt5-1)/2", (five.sqrt() - 1) / 2), ("16/113", Fraction(16, 113)),
            ("1/81", Fraction(1, 81)), ("5/9", Fraction(5, 9))]


def main():
    total, missed, onto = check_cantor(3)
    print(f"1. A = {{0, 1, 2}}: {total} functions A -> P(A); the diagonal set is")
    print(f"   missing from the image of {missed} of them; {onto} are onto.")
    print()
    print("2. The decimal diagonal (diagonal digit in brackets):")
    named = numbers()
    rows = [digits(x, 10) for _, x in named]
    for n, ((label, _), row) in enumerate(zip(named, rows)):
        shown = "".join(f"[{d}]" if i == n else str(d) for i, d in enumerate(row))
        print(f"   {label:12} 0.{shown}...")
    diag = diagonal_digits(rows)
    print("   d          = 0." + "".join(map(str, diag)) + "...")
    ok = all(diag[n] != rows[n][n] for n in range(len(rows)))
    print(f"   d differs from number n in digit n, for every n: {ok}")
    print()
    tricky = [[5] + [0] * 9] + [[0] * 10 for _ in range(9)]
    naive = [9 - row[n] for n, row in enumerate(tricky)]
    print("3. List 0.5000..., 0.0000..., 0.0000..., ... with the naive rule")
    print("   'replace x by 9 - x' gives 0." + "".join(map(str, naive))
          + "... = 0.5, which IS on the list.")
    print()
    print("Epistemic status: exhaustive for the 512 functions of part 1 and")
    print("exact for parts 2 and 3, but finite. The theorems - for every set")
    print("and every infinite list - are the lesson's proofs. Part 3 is a")
    print("counterexample to a careless version of the argument, not to Cantor.")


if __name__ == "__main__":
    main()
