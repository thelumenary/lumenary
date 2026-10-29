"""Two ways to read an expression: left to right, or by the convention.

A simple calculator works from left to right as you type, so it reads
2 + 3 x 4 as (2 + 3) x 4 = 20. The convention used in mathematics (and by
scientific calculators and programming languages) does multiplication and
division before addition and subtraction, giving 2 + 12 = 14. The program
evaluates some expressions both ways, then checks every expression
'a op b op c' with digits 1 to 9 and the four operations, and reports for
each pair of operations how often the two readings agree. Division is exact
(fractions), so nothing is rounded.
"""

import textwrap
from fractions import Fraction

EXPERIMENT = {
    "id": "expressions_and_unknowns_order",
    "title": "Left to right, or multiplication first?",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["expressions-and-unknowns"],
    "summary": (
        "Evaluates expressions both strictly left to right (like a simple "
        "calculator) and with the order-of-operations convention, using exact "
        "fractions. For all 11664 expressions a op b op c with digits 1-9 and "
        "the four operations it shows exactly when the two readings can "
        "disagree: when + or - is followed by x or /."
    ),
    "packages": [],
}

OPS = {
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "x": lambda x, y: x * y,
    "/": lambda x, y: x / y,
}


def tokens(text):
    """Split '2 + 3 x 4' into numbers (as Fractions) and symbols."""
    return [Fraction(t) if t.isdigit() else t for t in text.split()]


def left_to_right(toks):
    """Work strictly from left to right, as a simple calculator does."""
    value = toks[0]
    for i in range(1, len(toks), 2):
        value = OPS[toks[i]](value, toks[i + 1])
    return value


def by_convention(toks):
    """Brackets first, then x and /, then + and -, each left to right."""
    pos = 0

    def factor():
        nonlocal pos
        if toks[pos] == "(":
            pos += 1
            value = expression()
            pos += 1  # skip ")"
            return value
        pos += 1
        return toks[pos - 1]

    def term():
        nonlocal pos
        value = factor()
        while pos < len(toks) and toks[pos] in ("x", "/"):
            op = toks[pos]
            pos += 1
            value = OPS[op](value, factor())
        return value

    def expression():
        nonlocal pos
        value = term()
        while pos < len(toks) and toks[pos] in ("+", "-"):
            op = toks[pos]
            pos += 1
            value = OPS[op](value, term())
        return value

    return expression()

    """How many of the 729 'a op1 b op2 c' read the same both ways."""
def agreement(op1, op2):
    """How many of the 729 expressions 'a op1 b op2 c' read the same both ways."""
    same = 0
    for a in range(1, 10):
        for b in range(1, 10):
            for c in range(1, 10):
                toks = [Fraction(a), op1, Fraction(b), op2, Fraction(c)]
                same += left_to_right(toks) == by_convention(toks)
    return same


def main():
    print("Expression        left to right   by the convention")
    for text in ["2 + 3 x 4", "20 - 8 / 4", "18 / 3 x 2", "10 - 4 - 3",
                 "3 x 4 + 2"]:
        toks = tokens(text)
        print(f"{text:<17} {str(left_to_right(toks)):>13}"
              f"   {str(by_convention(toks)):>17}")
    print("(2 + 3) x 4       brackets first: "
          f"{by_convention(tokens('( 2 + 3 ) x 4'))}")
    print()
    print("Every 'a op1 b op2 c' with digits 1-9: out of 729, how many")
    print("give the same answer read both ways?")
    print("op1 \\ op2 " + "".join(f"{op2:>7}" for op2 in OPS))
    for op1 in OPS:
        row = "".join(f"{agreement(op1, op2):>7}" for op2 in OPS)
        print(f"   {op1}      {row}")
    print("The readings can only differ when + or - comes before x or /.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact (fractions, no rounding) and exhaustive for "
        "the 11664 expressions with three digits from 1 to 9. It shows when "
        "the convention matters; it does not show that the convention is "
        "'true'. The order of operations is an agreement, chosen so that "
        "expressions like 3 x 4 + 2 need no brackets.",
        width=78,
    ))


if __name__ == "__main__":
    main()
