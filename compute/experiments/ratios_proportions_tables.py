"""Is this table proportional? A classifier that uses exact fractions.

A table of pairs (x, y) comes from a proportional relationship y = kx when
every row with x != 0 has the same ratio y/x and every row with x = 0 has
y = 0. It comes from a straight line when the slope between consecutive rows
is constant. The experiment classifies six real-world tables, then shows the
practical difference: in a proportional table you may add two rows to get a
third, and in a merely linear table you may not.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "ratios_proportions_tables",
    "title": "Proportional, linear or neither? Classifying tables exactly",
    "evidence": ["exact"],
    "lessons": ["ratios-proportions"],
    "summary": (
        "Classifies tables of (x, y) pairs as proportional (constant ratio "
        "y/x, through the origin), linear but not proportional (constant "
        "slope only) or not linear, using exact fractions; finds the constant "
        "of proportionality; and shows that adding two rows of a table gives "
        "a valid row only for proportional tables. Exact for the tables shown; "
        "a finite table can never prove what happens between its rows."
    ),
    "packages": [],
}

TABLES = {
    "millet flour (people, cups)": [(4, 6), (6, 9), (10, 15), (14, 21)],
    "euros to CFA francs": [(1, "655.957"), (20, "13119.14"),
                            (50, "32797.85")],
    "taxi (km, fare)": [(1, 350), (2, 500), (5, 950), (8, 1400)],
    "square (side, perimeter)": [(1, 4), (2, 8), (5, 20)],
    "square (side, area)": [(1, 1), (2, 4), (3, 9), (5, 25)],
    "ages (Amara, brother)": [(5, 8), (10, 13), (20, 23)],
}


def as_pairs(table):
    """Convert table entries to exact Fractions (strings allowed)."""
    return [(Fraction(x), Fraction(y)) for x, y in table]


def constant_of_proportionality(table):
    """Return k if y = k*x for every row, else None."""
    pairs = as_pairs(table)
    ratios = {y / x for x, y in pairs if x != 0}
    if len(ratios) != 1 or any(y != 0 for x, y in pairs if x == 0):
        return None
    return ratios.pop()


def is_linear(table):
    """True if the slopes between consecutive rows (sorted by x) agree."""
    pairs = sorted(as_pairs(table))
    slopes = {(y2 - y1) / (x2 - x1)
              for (x1, y1), (x2, y2) in zip(pairs, pairs[1:])}
    return len(slopes) <= 1


def classify(table):
    """'proportional', 'linear, not proportional' or 'not linear'."""
    if constant_of_proportionality(table) is not None:
        return "proportional"
    if is_linear(table):
        return "linear, not proportional"
    return "not linear"


def add_rows(table, i, j):
    """Add rows i and j of a table: (x_i + x_j, y_i + y_j)."""
    pairs = as_pairs(table)
    return pairs[i][0] + pairs[j][0], pairs[i][1] + pairs[j][1]


def taxi_fare(km):
    """The rule behind the taxi table: 200 to start, 150 per km."""
    return 200 + 150 * Fraction(km)


def main():
    print(f"{'table':<29}{'classification':<26}k = y/x")
    for name, table in TABLES.items():
        k = constant_of_proportionality(table)
        shown = "-" if k is None else (
            str(k) if k.denominator == 1 else f"{float(k):g}")
        print(f"{name:<29}{classify(table):<26}{shown}")
    print()
    print("Adding two rows of a table:")
    x, y = add_rows(TABLES["millet flour (people, cups)"], 0, 1)
    print(f"  flour: 4 people + 6 people -> {x} people need {y} cups;")
    print(f"         the rule y = 3x/2 gives {Fraction(3, 2) * x}: it works.")
    x, y = add_rows(TABLES["taxi (km, fare)"], 0, 1)
    print(f"  taxi:  1 km + 2 km -> adding fares predicts {y} for {x} km,")
    print(f"         but the real fare is {taxi_fare(x)}: the start fee of")
    print("         200 was counted twice.")
    print()
    print("Epistemic status: exact arithmetic on the rows shown. A table only")
    print("samples a relationship: these checks cannot see what happens")
    print("between or beyond the rows. Knowing the rule (y = kx) is what")
    print("makes a relationship proportional.")


if __name__ == "__main__":
    main()
