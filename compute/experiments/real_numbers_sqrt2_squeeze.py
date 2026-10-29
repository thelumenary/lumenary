"""Squeezing sqrt(2) between rationals, and searching for p^2 = 2 q^2.

The rational map p -> (2p + 2)/(p + 2) sends every positive rational with
p^2 < 2 to a *larger* one with the same property, and every rational with
p^2 > 2 to a *smaller* one with the same property. Iterating it in exact
rational arithmetic shows, case by case, why the set {q in Q : q^2 < 2} has
no largest element and no least rational upper bound. A brute-force search
then finds no solution of p^2 = 2 q^2 with 1 <= q <= 100000 (evidence only;
the lesson's descent argument is the proof), while the near misses
p^2 - 2 q^2 = +-1 show how close fractions can get to sqrt(2).
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "real_numbers_sqrt2_squeeze",
    "title": "Squeezing the square root of 2 between fractions",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["real-numbers"],
    "summary": (
        "Iterates the map p -> (2p + 2)/(p + 2) in exact rational arithmetic from "
        "below and from above sqrt(2), showing that no rational is the largest "
        "with p^2 < 2 or the least with p^2 > 2. Then searches all q up to "
        "100000 for p^2 = 2q^2 (none: evidence, not proof) and lists the near "
        "misses p^2 - 2q^2 = +-1."
    ),
    "packages": [],
}


def push(p):
    """The map p -> (2p + 2)/(p + 2), in exact arithmetic for Fractions."""
    return (2 * p + 2) / (p + 2)


def orbit(p0, steps):
    """Return [p0, push(p0), push(push(p0)), ...] with ``steps`` applications."""
    if steps < 0:
        raise ValueError("steps must be non-negative")
    values = [Fraction(p0)]
    for _ in range(steps):
        values.append(push(values[-1]))
    return values


def square_minus_two(p):
    """p^2 - 2 (exact for Fractions): negative below sqrt(2), positive above."""
    return p * p - 2


def solutions_sq_eq_two_sq(limit):
    """All (p, q) with 1 <= q <= limit and p^2 = 2 q^2 (there are none)."""
    found = []
    for q in range(1, limit + 1):
        p = math.isqrt(2 * q * q)
        if p * p == 2 * q * q:
            found.append((p, q))
    return found


def near_misses(limit):
    """Pairs (p, q), q <= limit, with p^2 - 2 q^2 = +1 or -1."""
    pairs = []
    for q in range(1, limit + 1):
        for p in (math.isqrt(2 * q * q), math.isqrt(2 * q * q) + 1):
            if abs(p * p - 2 * q * q) == 1:
                pairs.append((p, q))
    return pairs


def main():
    root = math.sqrt(2)
    for start, side in ((1, "below"), (2, "above")):
        print(f"Starting {side} sqrt(2) at p = {start}:")
        for p in orbit(start, 5):
            sign = "<" if square_minus_two(p) < 0 else ">"
            gap = abs(float(p) - root)
            print(f"  p = {str(p):>9}   p^2 {sign} 2   |p - sqrt 2| = {gap:.2e}")
    print("Each step stays on its side of sqrt(2) and gets closer: no rational")
    print("is the largest below sqrt(2) or the smallest above it.")
    print()
    limit = 100000
    sols = solutions_sq_eq_two_sq(limit)
    print(f"Solutions of p^2 = 2q^2 with 1 <= q <= {limit}: {len(sols)}")
    misses = near_misses(1000)
    print("Near misses p^2 - 2q^2 = +-1 with q <= 1000 (fractions p/q):")
    print("  " + ", ".join(f"{p}/{q}" for p, q in misses))
    print()
    print("Epistemic status: the orbits are exact rational computations, but")
    print("only finitely many steps; the lesson's algebra proves the pattern")
    print("for every p. The search is exhaustive only up to q = 100000; that")
    print("no solution exists at all is proved by infinite descent, not here.")


if __name__ == "__main__":
    main()
