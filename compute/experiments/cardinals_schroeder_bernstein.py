"""The Schroeder-Bernstein bijection, computed by following chains.

Given injections f : A -> B and g : B -> A, follow any a in A backwards:
a = g(b)?  b = f(a')?  a' = g(b')? ... The backward chain either stops in A
(at a point not of the form g(b)), stops in B (at a point not of the form
f(a)), or never stops. The proof in the lesson sets h(a) = f(a) when the chain
stops in A and h(a) = g^(-1)(a) otherwise; these are exactly the points of the
least fixed point S of the map S -> A minus g[B minus f[S]]. Here we compute h
for two examples: the closed and half-open unit intervals (on rational points,
with exact fractions), where h turns out to be the famous "halve the powers of
1/2" map, and the natural numbers and the integers. Evidence: exact
computation on finitely many points; bijectivity on the whole set is the
theorem.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "cardinals_schroeder_bernstein",
    "title": "Schroeder-Bernstein bijections by chain-chasing",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["cardinals"],
    "summary": (
        "Builds the Schroeder-Bernstein bijection h from two injections by "
        "classifying backward chains (stopping in A, stopping in B, or endless), "
        "for [0, 1] vs [0, 1) with f(x) = x/2 and g(y) = y on exact rational "
        "points, and for N vs Z. Checks injectivity and that every target in a "
        "finite window is hit. Exact, but only for finitely many points: "
        "bijectivity on the whole sets is the theorem."
    ),
    "packages": [],
}


def chain_type(a, f_inv, g_inv, limit=200):
    """Follow a in A backwards; return 'A', 'B' (where it stops) or 'endless'."""
    seen = set()
    x, side = a, "A"
    for _ in range(limit):
        if (x, side) in seen:
            return "endless"
        seen.add((x, side))
        prev = g_inv(x) if side == "A" else f_inv(x)
        if prev is None:
            return side
        x, side = prev, ("B" if side == "A" else "A")
    return "endless"


def sb_map(a, f, f_inv, g_inv):
    """The Schroeder-Bernstein bijection: f on A-stopping chains, else g^-1."""
    if chain_type(a, f_inv, g_inv) == "A":
        return f(a)
    return g_inv(a)


# Example 1: A = [0, 1], B = [0, 1), f(x) = x/2 (into B), g(y) = y (into A).
def f1(x):
    return x / 2


def f1_inv(y):
    return 2 * y if y <= Fraction(1, 2) else None


def g1_inv(x):
    return x if x < 1 else None


# Example 2: A = N, B = Z, f(n) = n, g(z) = 3z (z >= 0), -3z - 1 (z < 0).
def f2(n):
    return n


def f2_inv(z):
    return z if z >= 0 else None


def g2_inv(n):
    if n % 3 == 0:
        return n // 3
    if n % 3 == 2:
        return -(n + 1) // 3
    return None


def rational_points(max_den):
    """All fractions p/q in [0, 1] with q <= max_den, sorted."""
    pts = {Fraction(p, q) for q in range(1, max_den + 1) for p in range(q + 1)}
    return sorted(pts)


def main():
    print("Example 1: A = [0, 1], B = [0, 1), f(x) = x/2, g(y) = y.")
    for x in [Fraction(1), Fraction(1, 2), Fraction(1, 8), Fraction(3, 4),
              Fraction(1, 3), Fraction(0)]:
        kind = chain_type(x, f1_inv, g1_inv)
        label = "never stops" if kind == "endless" else f"stops in {kind}"
        print(f"   x = {str(x):>4}: backward chain {label:<11}  h(x) = "
              f"{sb_map(x, f1, f1_inv, g1_inv)}")
    pts = rational_points(30)
    images = [sb_map(x, f1, f1_inv, g1_inv) for x in pts]
    in_b = all(0 <= y < 1 for y in images)
    moved = sorted(x for x, y in zip(pts, images) if y != x)
    print(f"   {len(pts)} rational points with denominator <= 30:")
    print(f"   images in [0, 1): {in_b}; injective: "
          f"{len(set(images)) == len(images)}")
    print(f"   points moved: {[str(x) for x in reversed(moved)]}")
    print("   h halves 1, 1/2, 1/4, ... and fixes everything else.")
    print()
    print("Example 2: A = N, B = Z, f(n) = n, g(z) = 3z or -3z - 1.")
    h = [sb_map(n, f2, f2_inv, g2_inv) for n in range(3000)]
    print("   h(0..14) =", h[:15])
    window = set(range(-200, 201))
    hit = window <= set(h)
    print(f"   h injective on 0..2999: {len(set(h)) == len(h)}; "
          f"hits every z in -200..200: {hit}")
    kinds = [chain_type(n, f2_inv, g2_inv) for n in range(30)]
    print("   chains of 0..29 stop in A / B / never:",
          [kinds.count(k) for k in ("A", "B", "endless")])
    print()
    print("Epistemic status: exact arithmetic, checked on finitely many points")
    print(f"({len(pts)} rationals; 3000 natural numbers). That h is a bijection of the")
    print("whole sets is the Schroeder-Bernstein theorem, proved in the lesson;")
    print("the chain classification uses no choice, so the theorem holds in ZF.")


if __name__ == "__main__":
    main()
