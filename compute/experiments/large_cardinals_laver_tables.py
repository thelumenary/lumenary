"""Laver tables: finite algebras that large cardinals know about.

For n >= 0 let N = 2^n. The Laver table A_n is the unique operation * on
{1, ..., N} with p * 1 = p + 1 (mod N, so N * 1 = 1) that is left
self-distributive: p * (q * r) = (p * q) * (p * r). Richard Laver discovered
these tables in the study of elementary embeddings j : V_lambda -> V_lambda
(the rank-into-rank axiom I3). Each row is periodic, and Laver proved, assuming
I3, that the period of the first row tends to infinity as n grows. No proof
of this purely finite statement without large cardinals is known.

We build A_n for n <= 9 with the recursion p * (q + 1) = (p * q) * (p + 1),
filling rows from p = N downwards, check left self-distributivity
exhaustively for small n, and print the period of the first row.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "large_cardinals_laver_tables",
    "title": "Laver tables and the period of their first row",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["large-cardinals"],
    "summary": (
        "Builds the Laver tables A_n (n <= 9), checks left self-distributivity "
        "exhaustively for n <= 5, and computes the period of the first row "
        "(1, 1, 2, 4, 4, 8, 8, 8, 8, 16). Laver proved from the large cardinal axiom "
        "I3 that this period tends to infinity; exact computation for small n only, "
        "which says nothing about that limit."
    ),
    "packages": [],
}


def laver_table(n):
    """The table of A_n as a dict of rows: rows[p][q - 1] = p * q."""
    size = 2 ** n
    rows = {size: list(range(1, size + 1))}
    for p in range(size - 1, 0, -1):
        row = [p + 1]
        for _ in range(size - 1):
            row.append(rows[row[-1]][p])  # (p * q) * (p + 1)
        rows[p] = row
    return rows


def star(rows, p, q):
    """p * q in the table."""
    return rows[p][q - 1]


def is_left_distributive(rows):
    """Check p * (q * r) = (p * q) * (p * r) for all p, q, r."""
    size = len(rows)
    return all(
        star(rows, p, star(rows, q, r)) == star(rows, star(rows, p, q),
                                                star(rows, p, r))
        for p in range(1, size + 1)
        for q in range(1, size + 1)
        for r in range(1, size + 1)
    )


def period(row):
    """The least period of a list that repeats exactly."""
    for d in range(1, len(row) + 1):
        if len(row) % d == 0 and row == row[:d] * (len(row) // d):
            return d
    return len(row)


def main():
    print("  n   size   left-distributive   period of row 1   row 1 (start)")
    periods = []
    for n in range(10):
        rows = laver_table(n)
        check = str(is_left_distributive(rows)) if n <= 5 else "(not run)"
        per = period(rows[1])
        periods.append(per)
        start = " ".join(map(str, rows[1][:per][:6]))
        print(f"{n:>3}   {2 ** n:>4}   {check:>17}   {per:>15}   {start}")
    print()
    print(f"Periods of row 1 for n = 0..9: {periods}")
    a3 = laver_table(2)
    print("The table A_2 (rows p = 1..4, columns q = 1..4):")
    for p in range(1, 5):
        print("   " + " ".join(str(v) for v in a3[p]))
    print()
    print(textwrap.fill(
        "Epistemic status: exact computation of finitely many finite tables, "
        "with distributivity checked exhaustively for n <= 5. It cannot show "
        "that the period of row 1 tends to infinity. Laver proved that from "
        "the rank-into-rank axiom I3; Dougherty showed that the period first "
        "reaches 32 only for astronomically large n; whether ZFC alone proves "
        "that the period is unbounded is not known.",
        width=78,
    ))


if __name__ == "__main__":
    main()
