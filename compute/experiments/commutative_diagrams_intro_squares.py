"""Do the paths agree? Testing squares of functions by computer.

A square of functions commutes when both routes give the same output for
every input. The experiment (1) tests three squares on the integers -50..50
and reports the first input where the routes disagree; (2) hunts for
counterexamples to "f(a + b) = f(a) + f(b)"; (3) checks all 3125 functions
from {0, ..., 4} to itself and finds exactly 5 that preserve addition with
remainders, each "multiply by m"; (4) checks every way of filling a pair of
squares with functions on {0, 1}: pasting always works, the converse does
not. Parts 3 and 4 are exhaustive; parts 1 and 2 are evidence or refutation.
"""

from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "commutative_diagrams_intro_squares",
    "title": "Do the paths agree? Testing squares of functions",
    "evidence": ["exhaustive-finite", "counterexample", "exact"],
    "lessons": ["commutative-diagrams-intro"],
    "summary": (
        "Tests whether squares of functions commute on -50..50 and prints the "
        "first disagreement; searches for counterexamples to f(a + b) = f(a) + "
        "f(b) for 100x, x + 1, x*x, -3x and the Celsius-to-Fahrenheit rule; "
        "checks all 3125 functions on {0..4} and finds exactly 5 that preserve "
        "addition mod 5 (multiplication by m); and checks all 16384 fillings of "
        "two squares on {0, 1} to confirm pasting and refute its converse."
    ),
    "packages": [],
}


def around_zero(n):
    """The integers -n..n, ordered 0, -1, 1, -2, 2, ... so that searches
    report the smallest counterexample first."""
    return sorted(range(-n, n + 1), key=lambda x: (abs(x), x))


def first_disagreement(route1, route2, inputs):
    """The first input where the two routes differ, or None if they agree."""
    for x in inputs:
        if route1(x) != route2(x):
            return x
    return None


def add_counterexample(f, values, add=lambda a, b: a + b):
    """A pair (a, b) with f(a + b) != f(a) + f(b), or None. `add` is the
    addition used after applying f (for remainders it wraps around)."""
    for a in values:
        for b in values:
            if f(a + b) != add(f(a), f(b)):
                return (a, b)
    return None


def additive_maps_mod(n):
    """All functions f on {0..n-1} with f((a+b) % n) == (f(a)+f(b)) % n."""
    found = []
    for outputs in product(range(n), repeat=n):
        if all(outputs[(a + b) % n] == (outputs[a] + outputs[b]) % n
               for a in range(n) for b in range(n)):
            found.append(outputs)
    return found


def square_commutes(top, right, left, bottom, inputs):
    """right(top(x)) == bottom(left(x)) for every x; maps are tuples."""
    return all(right[top[x]] == bottom[left[x]] for x in inputs)


def pasting_counts():
    """Fill the two squares (7 maps on {0, 1}) in every way. Return
    (both squares commute, ... and the rectangle commutes too,
    rectangle commutes but the left square does not)."""
    maps = list(product((0, 1), repeat=2))
    both = both_and_outer = outer_not_left = 0
    for f, g, f2, g2, a, b, c in product(maps, repeat=7):
        left = square_commutes(f, b, a, f2, (0, 1))
        right = square_commutes(g, c, b, g2, (0, 1))
        gf = tuple(g[f[x]] for x in (0, 1))
        g2f2 = tuple(g2[f2[x]] for x in (0, 1))
        outer = square_commutes(gf, c, a, g2f2, (0, 1))
        if left and right:
            both += 1
            both_and_outer += outer
        if outer and not left:
            outer_not_left += 1
    return both, both_and_outer, outer_not_left


def main():
    xs = around_zero(50)
    print("1. Two routes around a square, inputs -50..50")
    tests = [
        ("double, +2  vs  +1, double", lambda x: 2 * x + 2, lambda x: 2 * (x + 1)),
        ("+1, double  vs  double, +1", lambda x: 2 * (x + 1), lambda x: 2 * x + 1),
        ("square      vs  double    ", lambda x: x * x, lambda x: 2 * x),
    ]
    for name, r1, r2 in tests:
        bad = first_disagreement(r1, r2, xs)
        agree = sum(r1(x) == r2(x) for x in xs)
        verdict = "agree on all 101" if bad is None else f"differ at {bad}"
        print(f"   {name}: {verdict} (agree on {agree})")
    print()
    print("2. Does f(a + b) = f(a) + f(b)? Search a, b in -20..20")
    vals = around_zero(20)
    rules = [("100x", lambda x: 100 * x), ("x + 1", lambda x: x + 1),
             ("x * x", lambda x: x * x), ("-3x", lambda x: -3 * x),
             ("C to F", lambda x: Fraction(9, 5) * x + 32)]
    for name, f in rules:
        cx = add_counterexample(f, vals)
        print(f"   {name:<7}", "no counterexample" if cx is None
              else f"fails at a, b = {cx[0]}, {cx[1]}")
    print()
    maps = additive_maps_mod(5)
    print("3. All 5^5 = 3125 functions on {0..4}, adding with remainders mod 5")
    print(f"   preserving addition: {len(maps)}")
    for m in maps:
        print(f"   {m}  = multiply by {m[1]}:",
              all(m[x] == m[1] * x % 5 for x in range(5)))
    print()
    both, outer, converse = pasting_counts()
    print("4. Pasting: all 4^7 = 16384 ways to fill two squares on {0, 1}")
    print(f"   both squares commute: {both}; rectangle commutes too: {outer}")
    print(f"   rectangle commutes but the left square does not: {converse}")
    print()
    print("Epistemic status: parts 3 and 4 are exhaustive, so they prove their")
    print("claims for these small sets; parts 1 and 2 refute with one")
    print("counterexample but only test the others. The lesson proves that")
    print("pasting always works and that additive maps are multiplications.")


if __name__ == "__main__":
    main()
