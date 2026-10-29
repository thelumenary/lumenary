"""Truth tables for and, or, not - and checking a law in every row.

Each of two statements p and q is either true or false, so there are only
four rows to consider. The program prints the truth tables of 'and', the
inclusive 'or', the exclusive 'one or the other but not both' and 'not'. It
then checks De Morgan's laws and 'not (not p) = p' in every row, and shows
the one row where the inclusive and exclusive 'or' disagree. Because there
are only four rows, checking all of them is a complete proof of these laws -
unlike checking examples of a claim about all whole numbers.
"""

import textwrap
from itertools import product

EXPERIMENT = {
    "id": "logic_statements_truth_tables",
    "title": "Truth tables: and, or, not in every row",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["logic-statements"],
    "summary": (
        "Prints the truth tables of and, inclusive or, exclusive or and not "
        "for two statements, checks De Morgan's laws and double negation in "
        "all four rows, and finds the single row where inclusive and "
        "exclusive or differ. Every case is checked, so for these laws the "
        "check is a complete proof."
    ),
    "packages": [],
}

ROWS = list(product([True, False], repeat=2))


def word(value):
    """'T' for true and 'F' for false."""
    return "T" if value else "F"


def inclusive_or(p, q):
    """True when at least one of p, q is true (the mathematician's 'or')."""
    return p or q


def exclusive_or(p, q):
    """True when exactly one of p, q is true ('one or the other, not both')."""
    return p != q


def same_in_every_row(rule1, rule2):
    """Do two rules give the same truth value in all four rows?"""
    return all(rule1(p, q) == rule2(p, q) for p, q in ROWS)


def rows_that_differ(rule1, rule2):
    """The rows (p, q) in which two rules give different truth values."""
    return [(p, q) for p, q in ROWS if rule1(p, q) != rule2(p, q)]


def main():
    print("p  q  | p and q | p or q | one but not both | not p")
    for p, q in ROWS:
        print(f"{word(p)}  {word(q)}  |    {word(p and q)}    |"
              f"   {word(inclusive_or(p, q))}    |"
              f"        {word(exclusive_or(p, q))}         |   {word(not p)}")
    print()
    print("not (p and q) = (not p) or (not q) in all 4 rows:",
          same_in_every_row(lambda p, q: not (p and q),
                            lambda p, q: (not p) or (not q)))
    print("not (p or q) = (not p) and (not q) in all 4 rows:",
          same_in_every_row(lambda p, q: not (p or q),
                            lambda p, q: (not p) and (not q)))
    print("not (not p) = p in all 4 rows:",
          same_in_every_row(lambda p, q: not (not p), lambda p, q: p))
    differ = rows_that_differ(inclusive_or, exclusive_or)
    print("Rows where 'or' and 'one but not both' differ:",
          ", ".join(f"p={word(p)}, q={word(q)}" for p, q in differ))
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive. Two statements can only be "
        "true or false in 4 combinations, and every combination was "
        "checked, so this is a complete proof of these laws. A check of "
        "many examples of a claim about all whole numbers is different: "
        "there are infinitely many cases, so examples cannot finish the job.",
        width=78,
    ))


if __name__ == "__main__":
    main()
