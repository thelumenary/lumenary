"""The chord-and-tangent group law over the rationals, in exact arithmetic.

We implement addition on a short Weierstrass curve y^2 = x^3 + a x + b with
Fraction arithmetic (None is the point at infinity, the identity). Then:

1. On y^2 = x^3 + 1 the point P = (2, 3) has order 6: its multiples are listed
   and every one has integer coordinates, as the Nagell-Lutz theorem demands
   of torsion points.
2. On Bachet's curve y^2 = x^3 - 2 the point P = (3, 5) has infinite order:
   2P is not integral, so (Nagell-Lutz) 2P is not torsion, hence neither is P.
   The number of digits of the denominators of nP grows roughly like n^2, the
   signature of the canonical height.
3. Associativity, the hard axiom, is checked on every triple of points of a
   curve over the finite field F_13 (exhaustive for that curve).

All arithmetic is exact. The order-6 computation is a complete proof for that
point; the associativity check covers one finite curve only.
"""

from fractions import Fraction
import itertools

EXPERIMENT = {
    "id": "arithmetic_geometry_group_law",
    "title": "The chord-and-tangent group law in exact arithmetic",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["arithmetic-geometry"],
    "summary": (
        "Implements the group law on y^2 = x^3 + ax + b with exact fractions. "
        "Shows that (2, 3) has order 6 on y^2 = x^3 + 1, that (3, 5) on "
        "y^2 = x^3 - 2 has multiples with rapidly growing denominators (quadratic "
        "growth of height), and checks associativity on all triples of points "
        "of a curve over F_13: exact, exhaustive for that one curve only."
    ),
    "packages": [],
}


def on_curve(P, a, b):
    """True if P is the point at infinity or satisfies y^2 = x^3 + a x + b."""
    if P is None:
        return True
    x, y = P
    return y * y == x ** 3 + a * x + b


def neg(P):
    """The negative of a point: reflect in the x-axis."""
    return None if P is None else (P[0], -P[1])


def add(P, Q, a):
    """Chord-and-tangent addition on y^2 = x^3 + a x + b (b is not needed)."""
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and y1 == -y2:
        return None  # vertical line: P + (-P) = O
    if x1 == x2:
        slope = (3 * x1 * x1 + a) / (2 * y1)  # tangent
    else:
        slope = (y2 - y1) / (x2 - x1)  # chord
    x3 = slope * slope - x1 - x2
    y3 = slope * (x3 - x1) + y1  # third intersection point
    return (x3, -y3)  # reflect it


def multiple(n, P, a):
    """n * P for n >= 0, by repeated addition."""
    R = None
    for _ in range(n):
        R = add(R, P, a)
    return R


def order(P, a, limit=20):
    """The order of P if it is at most `limit`, otherwise None."""
    R = P
    for n in range(1, limit + 1):
        if R is None:
            return n
        R = add(R, P, a)
    return None


def is_integral(P):
    """True for the point at infinity or a point with integer coordinates."""
    return P is None or (P[0].denominator == 1 and P[1].denominator == 1)


def add_mod(P, Q, a, p):
    """The same chord-and-tangent formulas over the field Z/pZ (p prime > 3)."""
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if x1 == x2:
        slope = (3 * x1 * x1 + a) * pow(2 * y1, -1, p) % p
    else:
        slope = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (slope * slope - x1 - x2) % p
    y3 = (slope * (x3 - x1) + y1) % p
    return (x3, -y3 % p)


def points_mod(a, b, p):
    """All points of y^2 = x^3 + a x + b over Z/pZ, the point at infinity first."""
    return [None] + [(x, y) for x in range(p) for y in range(p)
                     if (y * y - x ** 3 - a * x - b) % p == 0]


def associativity_failures(points, a, p):
    """Triples (P, Q, R) of points over Z/pZ with (P + Q) + R != P + (Q + R)."""
    bad = []
    for P, Q, R in itertools.product(points, repeat=3):
        if add_mod(add_mod(P, Q, a, p), R, a, p) != add_mod(P, add_mod(Q, R, a, p), a, p):
            bad.append((P, Q, R))
    return bad


def fmt(P):
    """Short text for a point."""
    return "O" if P is None else f"({P[0]}, {P[1]})"


def main():
    F = Fraction
    print("1. y^2 = x^3 + 1, P = (2, 3):")
    P = (F(2), F(3))
    for n in range(1, 7):
        print(f"   {n}P = {fmt(multiple(n, P, 0))}")
    print(f"   order of P = {order(P, 0)}; all multiples integral: "
          f"{all(is_integral(multiple(n, P, 0)) for n in range(1, 7))}")
    print()
    print("2. Bachet's curve y^2 = x^3 - 2, P = (3, 5):")
    a, b = F(0), F(-2)
    Q = (F(3), F(5))
    print(f"   2P = {fmt(multiple(2, Q, a))} (not integral, so P has")
    print("   infinite order by Nagell-Lutz)")
    print("    n   digits of denominator of x(nP)   ratio to n^2")
    R = None
    for n in range(1, 11):
        R = add(R, Q, a)
        assert on_curve(R, a, b)
        d = len(str(R[0].denominator))
        print(f"   {n:2d}   {d:30d}   {d / n ** 2:12.2f}")
    print()
    pts = points_mod(2, 3, 13)
    bad = associativity_failures(pts, 2, 13)
    print(f"3. y^2 = x^3 + 2x + 3 over F_13 has {len(pts)} points; "
          f"associativity fails")
    print(f"   for {len(bad)} of all {len(pts) ** 3} triples.")
    print()
    print("Epistemic status: exact arithmetic. Part 1 is a complete")
    print("computation of the order of (2, 3); that (3, 5) has infinite order")
    print("rests on the Nagell-Lutz theorem, quoted, not proved here. Part 3 is")
    print("exhaustive for one curve over one field; associativity in general is")
    print("a theorem (proved in the references, and in Mathlib).")


if __name__ == "__main__":
    main()
