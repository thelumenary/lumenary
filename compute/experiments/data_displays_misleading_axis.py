"""How a bar chart can mislead: an axis that does not start at zero.

Two schools collected paper for recycling: Riverside 52 kg and Hilltop
48 kg. The program draws the two bars in text twice - once with the axis
starting at 0 and once starting at 40 - and computes how many times taller
one bar *looks* than the other for several starting values. Finally it
checks, for every whole-number case up to 60, that starting the axis above
zero always makes the bigger bar look relatively bigger than it is.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap
from fractions import Fraction

EXPERIMENT = {
    "id": "data_displays_misleading_axis",
    "title": "Misleading bar charts: when the axis does not start at zero",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["data-displays"],
    "summary": (
        "Draws bars for 52 kg and 48 kg as text with the axis starting at 0 "
        "and at 40, and computes the apparent ratio of the bars for several "
        "starting values (from 13/12 up to 5). Then checks every whole-number "
        "case 0 < b < c < a <= 60 that a raised axis exaggerates the ratio. "
        "Exact; exhaustive only up to 60."
    ),
    "packages": [],
}

SCHOOLS = [("Riverside", 52), ("Hilltop", 48)]


def drawn_height(value, base):
    """The height of a bar when the axis starts at `base` instead of 0."""
    if value < base:
        raise ValueError("the bar would start below the axis")
    return value - base


def apparent_ratio(big, small, base):
    """How many times taller the bigger bar looks, as an exact fraction."""
    return Fraction(drawn_height(big, base), drawn_height(small, base))


def text_bar(value, base, per_char):
    """A bar of '#' characters: one '#' for every `per_char` units above base."""
    return "#" * int(drawn_height(value, base) / per_char)


def exaggeration_always(limit):
    """Check apparent ratio > true ratio for all 0 < b < c < a <= limit.

    Returns (number of cases checked, list of failures).
    """
    checked, failures = 0, []
    for a in range(1, limit + 1):
        for c in range(1, a):
            for b in range(1, c):
                checked += 1
                if not apparent_ratio(a, c, b) > Fraction(a, c):
                    failures.append((a, b, c))
    return checked, failures


def main():
    for base, per_char in ((0, 2), (40, Fraction(1, 3))):
        print(f"Axis starting at {base} kg:")
        for name, kg in SCHOOLS:
            print(f"  {name:<9} {kg} kg |{text_bar(kg, base, per_char)}")
    print()
    print("Axis starts at   bars drawn   looks this many times taller")
    for base in (0, 20, 30, 40, 44, 46, 47):
        r = apparent_ratio(52, 48, base)
        print(f"{base:>14}   {52 - base:>4} : {48 - base:<4}"
              f"   {str(r):>6} = {float(r):.2f}")
    print("True ratio: 52/48 = 13/12, only about 1.08.")
    print()
    checked, failures = exaggeration_always(60)
    print(f"Every whole-number case 0 < b < c < a <= 60: {checked} cases.")
    print(f"Cases where the raised axis did not exaggerate: {len(failures)}.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact arithmetic with fractions. The table is "
        "exact for these two schools, and the final check covers every "
        "whole-number case up to 60 (finite evidence only). The lesson's "
        "argument and the Lean module prove the rule for all whole numbers.",
        width=78,
    ))


if __name__ == "__main__":
    main()
