"""The mean as a fair share: levelling towers of cubes, one cube at a time.

Each child in a group has built a tower of cubes. To share fairly, we
repeatedly move one cube from a tallest tower to a shortest tower, until no
move can make things fairer. The program prints every step and compares the
final level with total / number of towers. Then it finds the mean of some
measurements in quarter centimetres, exactly, with fractions.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap
from fractions import Fraction

EXPERIMENT = {
    "id": "data_displays_fair_share",
    "title": "The mean as a fair share: levelling towers",
    "evidence": ["exact"],
    "lessons": ["data-displays"],
    "summary": (
        "Levels towers of cubes by moving one cube at a time from a tallest "
        "to a shortest tower, printing every step, and checks that the final "
        "level equals total / number of towers (and that the mean need not be "
        "a data value). Then computes the exact mean of measurements in "
        "quarters with fractions. Exact for these data sets."
    ),
    "packages": [],
}


def level_once(towers):
    """Move one cube from a tallest tower to a shortest tower, if that helps.

    Returns the new list of towers, or None when the tallest and shortest
    towers differ by at most one cube (no move can make it fairer).
    """
    tall = towers.index(max(towers))
    short = towers.index(min(towers))
    if towers[tall] - towers[short] <= 1:
        return None
    new = list(towers)
    new[tall] -= 1
    new[short] += 1
    return new


def level(towers):
    """Level the towers step by step; return the list of all stages."""
    stages = [list(towers)]
    while True:
        nxt = level_once(stages[-1])
        if nxt is None:
            return stages
        stages.append(nxt)


def mean(values):
    """The mean as an exact fraction: total divided by how many values."""
    if not values:
        raise ValueError("the mean of no values is not defined")
    return Fraction(sum(values), len(values))


def show(values):
    """Format a list of numbers or fractions compactly."""
    return " ".join(str(v) for v in values)


def main():
    names = ["Ana", "Ben", "Chen", "Dina"]
    towers = [4, 6, 8, 2]
    print("Towers:", ", ".join(f"{n} {t}" for n, t in zip(names, towers)))
    stages = level(towers)
    for i, stage in enumerate(stages[1:], start=1):
        print(f"  move {i}: {show(stage)}")
    m = mean(towers)
    answer = "yes" if m in towers else "no"
    print(f"Level {stages[-1][0]} = total {sum(towers)} / {len(towers)} towers"
          f" = {m}. Is {m} one of the towers? {answer}")
    print()
    odd = [3, 7, 2, 6]
    stages = level(odd)
    print(f"Towers {show(odd)}: after {len(stages) - 1} moves they are"
          f" {show(stages[-1])}.")
    print(f"They cannot be level with whole cubes: the fair share is"
          f" {sum(odd)}/{len(odd)} = {mean(odd)} = {float(mean(odd))}.")
    print()
    beans = [Fraction(9, 4), Fraction(5, 2), Fraction(5, 2), Fraction(11, 4),
             Fraction(13, 4), Fraction(7, 2), Fraction(7, 2), Fraction(15, 4)]
    print("Bean seedlings, heights in cm:", show(beans))
    total = sum(beans)
    mb = mean(beans)
    print(f"Total {total} cm, so the mean is {total} / {len(beans)}"
          f" = {mb} cm.")
    print(f"Check: mean x number of values = {mb * len(beans)} = total.")
    print(f"Is the mean one of the heights? {'yes' if mb in beans else 'no'}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact. Whole cubes and fractions are computed "
        "exactly, with no rounding. The program checks these data sets; the "
        "lesson and the Lean module prove that levelling always ends at "
        "total / number of towers when the towers can be levelled.",
        width=78,
    ))


if __name__ == "__main__":
    main()
