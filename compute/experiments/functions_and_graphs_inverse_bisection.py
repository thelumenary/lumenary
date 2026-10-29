"""Inverting a function that has no simple formula for its inverse.

f(x) = x^3 + x is strictly increasing, so it is injective and has an inverse
on its whole range. To evaluate the inverse at y we search for the x with
f(x) = y by bisection, using exact fractions: each step halves an interval
that is guaranteed to contain the answer, so after n steps the error is at
most (initial width) / 2^n. The experiment also shows why x^2 needs its domain
restricted to [0, oo) before it can be inverted.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "functions_and_graphs_inverse_bisection",
    "title": "Evaluating an inverse function by bisection",
    "evidence": ["exact", "numerical"],
    "lessons": ["functions-and-graphs"],
    "summary": (
        "Evaluates the inverse of the strictly increasing function f(x) = x^3 + x "
        "by bisection with exact fractions, with a guaranteed error bound "
        "(width / 2^n), checks that swapped points lie on the inverse's graph, and "
        "shows that x^2 fails to be injective until its domain is restricted."
    ),
    "packages": [],
}


def f(x):
    """The strictly increasing function x^3 + x."""
    return x ** 3 + x


def bisect_inverse(func, y, lo, hi, steps):
    """Find x in [lo, hi] with func(x) = y for an increasing ``func``.

    Requires func(lo) <= y <= func(hi). Returns (lo, hi) after ``steps``
    halvings; the true x always lies in the returned interval.
    """
    lo, hi = Fraction(lo), Fraction(hi)
    if not func(lo) <= y <= func(hi):
        raise ValueError("y is not between func(lo) and func(hi)")
    for _ in range(steps):
        mid = (lo + hi) / 2
        if func(mid) <= y:
            lo = mid
        else:
            hi = mid
    return lo, hi


def inverse(y, steps=40):
    """Approximate f^(-1)(y) as the midpoint of the final bisection interval."""
    bound = abs(Fraction(y)) + 1  # f(bound) >= bound >= |y|
    lo, hi = bisect_inverse(f, Fraction(y), -bound, bound, steps)
    return (lo + hi) / 2, (hi - lo) / 2


def collisions(func, points):
    """Pairs of different inputs among ``points`` with the same output."""
    pts = sorted(set(points))
    return [(a, b) for i, a in enumerate(pts) for b in pts[i + 1:]
            if func(a) == func(b)]


def main():
    print("f(x) = x^3 + x is strictly increasing, so it has an inverse g.")
    print("g(y) by 40 steps of exact bisection; error bound = half-width:")
    for y in [2, 10, 30, -10]:
        x, err = inverse(y)
        print(f"  g({y:3d}) ~ {float(x):.12f}   |error| <= {float(err):.1e}"
              f"   f(x) - y = {float(f(x) - y):.1e}")
    print("  exact values: g(2) = 1, g(10) = 2, g(30) = 3, g(-10) = -2")
    print()
    print("reflection: (a, f(a)) on the graph of f gives (f(a), a) on g's:")
    for a in [Fraction(1, 2), Fraction(3, 2)]:
        x, err = inverse(f(a))
        print(f"  a = {a}: f(a) = {f(a)}, g(f(a)) ~ {float(x):.10f}"
              f" (within {float(err):.1e} of {a})")
    print()
    grid = [Fraction(n, 2) for n in range(-6, 7)]
    sq = collisions(lambda t: t * t, grid)
    print(f"x^2 on -3..3 in steps of 1/2: {len(sq)} pairs with equal outputs,")
    print(f"  e.g. {sq[0][0]} and {sq[0][1]}: not injective, no inverse on R.")
    pos = collisions(lambda t: t * t, [t for t in grid if t >= 0])
    print(f"  restricted to x >= 0: {len(pos)} collisions; the inverse is sqrt.")
    print()
    print("Epistemic status: bisection with exact fractions gives a rigorous")
    print("enclosure: since f is increasing and continuous, the true inverse value")
    print("lies in the final interval, so the error bound is guaranteed, not")
    print("estimated. Only the printed decimals are rounded. The collision count")
    print("is an exhaustive check of a finite grid, not a proof for all reals.")


if __name__ == "__main__":
    main()
