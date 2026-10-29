"""A class survey: tallies, a picture graph, and when totals add up.

Twenty-four children answer "How did you come to school today?". We sort
the answers into categories, draw a tally chart (a gate of five is drawn as
||||\\) and a picture graph, and answer "which is most?" and "how many
more?". Then we show two things that can go wrong: pictures of different
sizes make row lengths misleading, and letting a child choose two answers
makes the totals add up to more than the number of children. Finally we
check every possible way six children could answer a four-category question:
the totals always add up to six.

All counts are exact. The exhaustive check covers six children and four
categories only; the lesson explains why the totals add up for any survey in
which each answer goes into exactly one category.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
import textwrap

EXPERIMENT = {
    "id": "data_and_tallies_survey",
    "title": "A class survey: tallies, picture graphs and totals",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["data-and-tallies"],
    "summary": (
        "Tallies 24 survey answers into four categories, draws a tally chart and "
        "a picture graph, answers 'most' and 'how many more', shows how pictures "
        "of different sizes mislead and how multiple answers overcount, and "
        "checks all 4,096 ways six children can answer that the totals add up "
        "to six. Exact; the exhaustive check is for that small case only."
    ),
    "packages": [],
}

CATEGORIES = ("walk", "bus", "bike", "car")

#: The class's answers, in the order the children were asked.
ANSWERS = (
    "walk", "bus", "walk", "car", "bike", "walk", "bus", "walk",
    "bike", "bus", "walk", "car", "walk", "bus", "bike", "walk",
    "bus", "walk", "bike", "bus", "car", "walk", "bus", "bike",
)

#: Fruits four children like, when several answers are allowed.
LIKES = (("mango",), ("banana", "mango"), ("papaya",), ("mango", "papaya"))

GATE = "||||\\"


def tally(answers, categories=CATEGORIES):
    """Count the answers in each category, keeping the categories' order.

    Every answer must belong to exactly one category, so an answer that is
    not one of the categories is an error.
    """
    counts = {c: 0 for c in categories}
    for answer in answers:
        if answer not in counts:
            raise ValueError(f"answer {answer!r} is not one of the categories")
        counts[answer] += 1
    return counts


def tally_marks(n):
    """Draw n tally marks, grouped in gates of five."""
    if n < 0:
        raise ValueError("cannot draw a negative number of marks")
    gates, loose = divmod(n, 5)
    return " ".join([GATE] * gates + (["|" * loose] if loose else []))


def marks_to_number(marks):
    """Read a tally drawn by tally_marks: five per gate, one per loose mark."""
    return sum(5 if group == GATE else len(group) for group in marks.split())


def picture_row(n, picture="o"):
    """A row of n equal pictures, separated by single spaces."""
    return " ".join([picture] * n)


def most_and_fewest(counts):
    """The categories with the largest and with the smallest count."""
    top, low = max(counts.values()), min(counts.values())
    return ([c for c, n in counts.items() if n == top],
            [c for c, n in counts.items() if n == low])


def every_survey_adds_up(children, categories=CATEGORIES):
    """Check every possible survey of ``children`` children.

    Returns (surveys checked, True if the totals always equal ``children``).
    """
    checked, ok = 0, True
    for survey in product(categories, repeat=children):
        checked += 1
        ok = ok and sum(tally(survey, categories).values()) == children
    return checked, ok


def multi_choice_totals(choices, options):
    """Totals when each child may choose several options."""
    return {o: sum(o in chosen for chosen in choices) for o in options}


def main():
    counts = tally(ANSWERS)
    print(f'Survey: "How did you come to school today?" ({len(ANSWERS)} '
          "children)")
    print("Tally chart:")
    for cat, n in counts.items():
        print(f"  {cat:<5} {tally_marks(n):<12} {n:>2}")
    print("Picture graph (one o = one child):")
    for cat, n in counts.items():
        print(f"  {cat:<5} {picture_row(n)}")
    most, fewest = most_and_fewest(counts)
    print(f"Most: {', '.join(most)}. Fewest: {', '.join(fewest)}. "
          f"Walk compared with bus: {counts['walk'] - counts['bus']} more walk.")
    parts = " + ".join(str(n) for n in counts.values())
    print(f"Totals: {parts} = {sum(counts.values())}, "
          f"the number of children asked.")
    print()
    print("Same data, unequal pictures (car drawn wider):")
    rows = [("bike", picture_row(counts["bike"])),
            ("car", picture_row(counts["car"], "[car]"))]
    for cat, row in rows:
        print(f"  {cat:<5} {row:<18} count {counts[cat]}, "
              f"row length {len(row)}")
    print("  The car row is longer, but more children came by bike.")
    print()
    checked, ok = every_survey_adds_up(6)
    print(f"Every way 6 children can answer: {checked:,} surveys, "
          f"totals always 6: {ok}")
    totals = multi_choice_totals(LIKES, ("mango", "banana", "papaya"))
    listed = ", ".join(f"{f} {n}" for f, n in totals.items())
    print(f"Fruits liked, several answers allowed: {listed}")
    print(f"  totals {sum(totals.values())}, but only {len(LIKES)} children "
          "were asked: some were counted twice.")
    print()
    print(textwrap.fill(
        "Epistemic status: all counts are exact. The check that totals add up "
        f"covers all {checked:,} surveys of six children with four categories, "
        "and nothing else; why the totals add up whenever each answer goes "
        "into exactly one category is explained (and proved in Lean) in the "
        "lesson.",
        width=78,
    ))


if __name__ == "__main__":
    main()
