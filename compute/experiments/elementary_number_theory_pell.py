"""Pell's equation x^2 - d y^2 = 1 solved by continued fractions.

The continued fraction of sqrt(d), for d not a square, is periodic:
sqrt(d) = [a0; a1, ..., a_r] with the block a1..a_r repeating. The convergents
h/k satisfy h^2 - d k^2 = (-1)^(i+1) q_(i+1), and the fundamental solution of
Pell's equation is the convergent just before the end of the first period (or
of the second, when the period length r is odd). The program runs the exact
integer algorithm, checks each answer, and composes the fundamental solution
with itself (Brahmagupta's composition) to produce the next solutions.
"""

from math import isqrt

EXPERIMENT = {
    "id": "elementary_number_theory_pell",
    "title": "Pell's equation by continued fractions",
    "evidence": ["exact"],
    "lessons": ["elementary-number-theory"],
    "summary": (
        "Computes the periodic continued fraction of sqrt(d) with exact integer "
        "arithmetic, reads off the fundamental solution of x^2 - d y^2 = 1 for "
        "every non-square d up to 30 and for d = 61 and 109, verifies each solution "
        "exactly, and generates further solutions by composition. Exact for the d "
        "shown; that the method always works is proved in the lesson."
    ),
    "packages": [],
}


def sqrt_continued_fraction(d):
    """(a0, period) for sqrt(d), d > 0 not a square, by the exact (m, q, a) recursion."""
    a0 = isqrt(d)
    if a0 * a0 == d:
        raise ValueError("d must not be a perfect square")
    m, q, a = 0, 1, a0
    period = []
    while a != 2 * a0:
        m = a * q - m
        q = (d - m * m) // q
        a = (a0 + m) // q
        period.append(a)
    return a0, period


def fundamental_solution(d):
    """Least x > 1, y > 0 with x^2 - d y^2 = 1, from the convergents of sqrt(d)."""
    a0, period = sqrt_continued_fraction(d)
    r = len(period)
    terms = [a0] + (period * 2)[: (r if r % 2 == 0 else 2 * r) - 1]
    h_prev, h = 1, terms[0]
    k_prev, k = 0, 1
    for a in terms[1:]:
        h_prev, h = h, a * h + h_prev
        k_prev, k = k, a * k + k_prev
    return h, k


def compose(s, t, d):
    """Brahmagupta's composition of two solutions (x1 + y1 sqrt d)(x2 + y2 sqrt d)."""
    (x1, y1), (x2, y2) = s, t
    return x1 * x2 + d * y1 * y2, x1 * y2 + x2 * y1


def brute_force(d, limit):
    """Least y in 1..limit with d y^2 + 1 a square, as (x, y), or None."""
    for y in range(1, limit + 1):
        x2 = d * y * y + 1
        x = isqrt(x2)
        if x * x == x2:
            return x, y
    return None


def main():
    print(" d  period of sqrt(d)      fundamental solution (x, y)")
    ok = True
    for d in range(2, 31):
        if isqrt(d) ** 2 == d:
            continue
        a0, period = sqrt_continued_fraction(d)
        x, y = fundamental_solution(d)
        ok &= x * x - d * y * y == 1
        if d <= 14 or d in (19, 22, 29):
            shown = "[" + str(a0) + "; " + ",".join(map(str, period)) + "]"
            print(f"{d:>2}  {shown:<21}  ({x}, {y})")
    print(f"every non-square d <= 30 solved and checked exactly: {ok}")
    agree = all(brute_force(d, 2000) == fundamental_solution(d)
                for d in range(2, 31) if isqrt(d) ** 2 != d)
    print(f"brute force agrees for d <= 30 (y <= 2000): {agree}")
    for d in (61, 109):
        x, y = fundamental_solution(d)
        print(f"d = {d}: x = {x}, y = {y}")
        print(f"        x^2 - {d} y^2 = {x * x - d * y * y}")
    s = fundamental_solution(2)
    powers = [s]
    for _ in range(4):
        powers.append(compose(powers[-1], s, 2))
    print("x^2 - 2y^2 = 1: the powers of (3, 2) under composition are")
    print("  " + ", ".join(map(str, powers)))
    print()
    print("Epistemic status: exact integer computations, each solution verified")
    print("by substitution. That the continued-fraction method always finds the")
    print("fundamental solution, and that every solution is a power of it, are")
    print("theorems (see the lesson); the runs here are illustrations.")


if __name__ == "__main__":
    main()
