"""Which rule made this table? Searching input-output rules.

A table of inputs and outputs is evidence about a rule. The program tries
every rule of the form 'multiply by a, then add b' (a x n + b) with a and b
from 0 to 10 and lists those that fit the first rows of a table. One row
fits several rules; two rows pin down one rule of this kind - but a rule of
a different kind (n x n + 3) also fits those two rows, and only a third row
tells them apart. Finally it works backwards: which input gives a chosen
output, found by undoing the rule's steps in reverse order and checked by
running the rule forwards.
"""

import textwrap

EXPERIMENT = {
    "id": "expressions_and_unknowns_rules",
    "title": "Which rule made this table?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["expressions-and-unknowns"],
    "summary": (
        "Tries all 121 rules 'multiply by a, then add b' (a, b from 0 to 10) "
        "against the rows of the table 1 -> 4, 2 -> 7, 3 -> 10, 4 -> 13. One "
        "row fits five rules, two rows fit one; a rule of another kind, "
        "n x n + 3, also fits two rows. Then it undoes 3 x n + 1 to find "
        "inputs from outputs and checks them forwards."
    ),
    "packages": [],
}

TABLE = [(1, 4), (2, 7), (3, 10), (4, 13)]


def fits(rule, rows):
    """Does the rule give the right output for every row (input, output)?"""
    return all(rule(n) == out for n, out in rows)


def linear_rules_that_fit(rows, largest=10):
    """All (a, b) with 0 <= a, b <= largest such that a x n + b fits."""
    return [(a, b)
            for a in range(largest + 1)
            for b in range(largest + 1)
            if fits(lambda n, a=a, b=b: a * n + b, rows)]


def square_plus_three(n):
    """A rule of a different kind: n x n + 3."""
    return n * n + 3


def undo_three_n_plus_one(output):
    """Undo 'multiply by 3, then add 1' in reverse: take 1, then divide by 3.

    Returns None when there is no whole-number input."""
    if output < 1 or (output - 1) % 3 != 0:
        return None
    return (output - 1) // 3


def main():
    print("The table: " + ", ".join(f"{n} -> {out}" for n, out in TABLE))
    print("Rules 'a x n + b' (a, b from 0 to 10) that fit the first rows:")
    for k in range(1, len(TABLE) + 1):
        found = linear_rules_that_fit(TABLE[:k])
        rules = ", ".join(f"{a} x n + {b}" for a, b in found)
        rows = "row: " if k == 1 else "rows:"
        print(f"  {k} {rows} {rules}")
    print()
    print("A different kind of rule: n x n + 3")
    for k in (2, 3):
        print(f"  fits the first {k} rows:"
              f" {fits(square_plus_three, TABLE[:k])}")
    print("  (3 x 3 + 3 = 12, but the table says 3 -> 10.)")
    print()
    print("Working backwards from outputs of 3 x n + 1:")
    for output in (22, 31, 100, 24):
        n = undo_three_n_plus_one(output)
        if n is None:
            print(f"  output {output}: no whole-number input")
        else:
            print(f"  output {output}: input {n}"
                  f"  (check: 3 x {n} + 1 = {3 * n + 1})")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive, but only for rules of the "
        "form a x n + b with a and b from 0 to 10. A table with a few rows "
        "never proves which rule made it - other kinds of rules can fit the "
        "same rows. Knowing the rule, the backward answers are certain: each "
        "is checked by running the rule forwards.",
        width=78,
    ))


if __name__ == "__main__":
    main()
