"""The simplex method in exact arithmetic, with the dual read off at the end.

A small workshop makes two products. Product 1 uses 1 hour of workshop A and 3
hours of workshop C; product 2 uses 2 hours of workshop B and 2 hours of C.
Each week A, B and C have 4, 12 and 18 hours. Profits are 3 and 5 per unit:

    maximise 3x + 5y  subject to  x <= 4,  2y <= 12,  3x + 2y <= 18,  x, y >= 0.

The program runs the tableau simplex method with exact fractions, once with
Dantzig's rule (enter the variable with the largest reduced profit) and once
with Bland's rule (smallest index), and prints the vertices visited. The final
tableau also contains the optimal dual solution - the "shadow prices" of the
three workshops - and the program checks strong duality and complementary
slackness, then shows the method detecting an unbounded problem.

Exact rational arithmetic: an exact computation for these problems.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "optimisation_simplex",
    "title": "The simplex method and LP duality, in exact arithmetic",
    "evidence": ["exact"],
    "lessons": ["optimisation"],
    "summary": (
        "Solves a small production linear program with the tableau simplex "
        "method in exact fractions, under Dantzig's and Bland's pivoting rules, "
        "prints the vertices visited, reads the dual solution (shadow prices) "
        "from the final tableau, verifies equal primal and dual values and "
        "complementary slackness, and detects an unbounded problem."
    ),
    "packages": [],
}


def simplex(a, b, c, rule="dantzig"):
    """Maximise c.x subject to a x <= b, x >= 0, assuming b >= 0.

    Returns (status, x, y, value, path) where status is "optimal" or
    "unbounded", y is the dual solution and path lists the vertices visited.
    """
    m, n = len(a), len(c)
    rows = [[Fraction(v) for v in a[i]] + [Fraction(int(i == j)) for j in
            range(m)] + [Fraction(b[i])] for i in range(m)]
    obj = [Fraction(-v) for v in c] + [Fraction(0)] * (m + 1)
    basis = [n + i for i in range(m)]

    def vertex():
        x = [Fraction(0)] * n
        for i, var in enumerate(basis):
            if var < n:
                x[var] = rows[i][-1]
        return tuple(x)

    path = [vertex()]
    while True:
        candidates = [j for j in range(n + m) if obj[j] < 0]
        if not candidates:
            break
        col = (min(candidates, key=lambda j: (obj[j], j)) if rule == "dantzig"
               else min(candidates))
        ratios = [(rows[i][-1] / rows[i][col], basis[i], i)
                  for i in range(m) if rows[i][col] > 0]
        if not ratios:
            return "unbounded", None, None, None, path
        _, _, r = min(ratios)
        piv = rows[r][col]
        rows[r] = [v / piv for v in rows[r]]
        for i in range(m):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [u - f * v for u, v in zip(rows[i], rows[r])]
        f = obj[col]
        obj = [u - f * v for u, v in zip(obj, rows[r])]
        basis[r] = col
        path.append(vertex())
    y = tuple(obj[n:n + m])
    return "optimal", vertex(), y, obj[-1], path


def dot(u, v):
    return sum(Fraction(p) * Fraction(q) for p, q in zip(u, v))


A = [[1, 0], [0, 2], [3, 2]]
B = [4, 12, 18]
C = [3, 5]


def show(v):
    return "(" + ", ".join(str(t) for t in v) + ")"


def main():
    print("maximise 3x + 5y  s.t.  x <= 4, 2y <= 12, 3x + 2y <= 18, x, y >= 0")
    for rule in ("dantzig", "bland"):
        status, x, y, value, path = simplex(A, B, C, rule)
        print(f"{rule:>8} rule: vertices " +
              " -> ".join(show(p) for p in path) + f"; value {value}")
    status, x, y, value, _ = simplex(A, B, C)
    print("optimal x =", show(x), " dual y (shadow prices) =", show(y))
    aty = [dot([row[j] for row in A], y) for j in range(2)]
    ax = [dot(row, x) for row in A]
    print("dual feasible: A^T y =", show(aty), ">= c =", show(C),
          " y >= 0:", all(v >= 0 for v in y))
    print(f"primal value c.x = {dot(C, x)},  dual value b.y = {dot(B, y)}")
    slack = [bi - v for bi, v in zip(B, ax)]
    print("complementary slackness: y_i * slack_i =",
          show(yi * s for yi, s in zip(y, slack)))
    print("   (workshop A has slack 2 hours, so its shadow price is 0)")
    print()
    status, *_ = simplex([[1, -1]], [1], [1, 1])
    print("maximise x + y s.t. x - y <= 1:", status,
          "(a column with no positive entry)")
    print()
    print("Epistemic status: exact rational arithmetic, so the optimal vertex,\n"
          "the dual solution and the equality of the two values are exact for\n"
          "this problem. That equality for every LP with an optimum is the\n"
          "strong duality theorem, proved in the references; weak duality and\n"
          "complementary slackness are proved in the lesson and in Lean.")


if __name__ == "__main__":
    main()
