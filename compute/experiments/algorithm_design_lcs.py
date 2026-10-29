"""Longest common subsequence: the dynamic-programming table, and its savings.

The length L(i, j) of a longest common subsequence of the first i letters of
x and the first j letters of y satisfies L(i, j) = L(i-1, j-1) + 1 when the
i-th and j-th letters agree, and max(L(i-1, j), L(i, j-1)) otherwise. We fill
the (m+1) x (n+1) table for the classic example ABCBDAB / BDCABA, recover a
longest common subsequence by walking back through the table, and compare
the number of table cells with the number of calls made by the same
recursion without memory, on seeded random DNA strings.
"""

import random

EXPERIMENT = {
    "id": "algorithm_design_lcs",
    "title": "Longest common subsequence: table, traceback and savings",
    "evidence": ["exact", "experimental"],
    "lessons": ["algorithm-design"],
    "summary": (
        "Fills the dynamic-programming table for the longest common subsequence "
        "of ABCBDAB and BDCABA, recovers an optimal subsequence by traceback, "
        "and counts how many calls the plain recursion makes on seeded random "
        "DNA strings compared with the (m+1)(n+1) cells of the table."
    ),
    "packages": [],
}


def lcs_table(x, y):
    """The (len(x)+1) x (len(y)+1) table of LCS lengths of prefixes."""
    m, n = len(x), len(y)
    table = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if x[i - 1] == y[j - 1]:
                table[i][j] = table[i - 1][j - 1] + 1
            else:
                table[i][j] = max(table[i - 1][j], table[i][j - 1])
    return table


def traceback(x, y, table):
    """One longest common subsequence, read off the table from the end."""
    i, j, out = len(x), len(y), []
    while i > 0 and j > 0:
        if x[i - 1] == y[j - 1]:
            out.append(x[i - 1])
            i, j = i - 1, j - 1
        elif table[i - 1][j] >= table[i][j - 1]:
            i -= 1
        else:
            j -= 1
    return "".join(reversed(out))


def is_subsequence(s, t):
    """True if s can be obtained from t by deleting letters."""
    it = iter(t)
    return all(ch in it for ch in s)


def naive_calls(x, y):
    """(LCS length, number of calls) for the recursion without memory."""
    calls = 0

    def rec(i, j):
        nonlocal calls
        calls += 1
        if i == 0 or j == 0:
            return 0
        if x[i - 1] == y[j - 1]:
            return rec(i - 1, j - 1) + 1
        return max(rec(i - 1, j), rec(i, j - 1))

    return rec(len(x), len(y)), calls


def main():
    x, y = "ABCBDAB", "BDCABA"
    table = lcs_table(x, y)
    print(" " * 6 + "".join(f"{c:>3}" for c in y))
    for i, row in enumerate(table):
        label = " " if i == 0 else x[i - 1]
        print(f"  {label} " + " ".join(str(v).rjust(2) for v in row))
    z = traceback(x, y, table)
    print(f"LCS length {table[-1][-1]}; one LCS: {z}; subsequence of both:"
          f" {is_subsequence(z, x) and is_subsequence(z, y)}")
    print()
    rng = random.Random(42)
    print(" length  LCS  table cells  calls without memory")
    for n in (4, 6, 8, 10, 12):
        a = "".join(rng.choice("ACGT") for _ in range(n))
        b = "".join(rng.choice("ACGT") for _ in range(n))
        length, calls = naive_calls(a, b)
        assert length == lcs_table(a, b)[-1][-1]
        print(f"{n:7d} {length:4d} {(n + 1) ** 2:12d} {calls:21d}")
    print()
    print("Epistemic status: the table and traceback are exact computations")
    print("for one example; the lesson proves the recurrence correct for all")
    print("inputs (and Lean checks it). The call counts are measurements on a")
    print("few seeded random strings: they illustrate exponential growth of")
    print("the plain recursion but are not a worst-case analysis.")


if __name__ == "__main__":
    main()
