"""Counting points of curves over the finite fields F_p.

A variety defined over the integers can be reduced modulo a prime p and its
points over F_p counted. We count, by brute force over all points of the
projective plane P^2(F_p):

* P^2(F_p) itself, which has p^2 + p + 1 points (proved in the lesson and in
  Lean);
* the conic x^2 + y^2 = z^2, which is isomorphic to the projective line and
  so has p + 1 points for odd p;
* the cuspidal cubic y^2 z = x^3, which is in bijection with P^1 (p + 1
  points) although it is not isomorphic to it;
* the elliptic curve E: y^2 z = x^3 - x z^2, whose number of points
  p + 1 - a_p satisfies Hasse's theorem |a_p| <= 2 sqrt(p), has a_p = 0
  whenever p = 3 (mod 4) (E has complex multiplication by Z[i]), and for
  p = 1 (mod 4) has a_p/2 equal to the odd number a in p = a^2 + b^2.

Exhaustive and exact for the primes listed; the general statements are
theorems (Hasse 1933; Deuring 1941), not consequences of this computation.
"""

import math

EXPERIMENT = {
    "id": "algebraic_geometry_points_mod_p",
    "title": "Points of curves over finite fields",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["algebraic-geometry"],
    "summary": (
        "Counts the points of the projective plane, a conic, the cuspidal "
        "cubic and the elliptic curve y^2 = x^3 - x over F_p for all primes "
        "3 <= p < 60, by brute force over P^2(F_p). Confirms p^2 + p + 1, "
        "p + 1, p + 1, Hasse's bound |a_p| <= 2 sqrt(p), a_p = 0 for "
        "p = 3 mod 4 and p = (a_p/2)^2 + b^2 for p = 1 mod 4 in that range; "
        "exhaustive for these primes only."
    ),
    "packages": [],
}


def primes_between(lo, hi):
    """Primes p with lo <= p < hi."""
    return [p for p in range(max(lo, 2), hi)
            if all(p % q for q in range(2, math.isqrt(p) + 1))]


def projective_points(p):
    """One representative of each point of P^2(F_p).

    The representatives are (x, y, 1), (x, 1, 0) and (1, 0, 0).
    """
    pts = [(x, y, 1) for x in range(p) for y in range(p)]
    pts += [(x, 1, 0) for x in range(p)]
    pts.append((1, 0, 0))
    return pts


def count_points(form, p):
    """Number of points of P^2(F_p) where the homogeneous form vanishes."""
    return sum(1 for x, y, z in projective_points(p)
               if form(x, y, z) % p == 0)


def conic(x, y, z):
    """The circle x^2 + y^2 = z^2."""
    return x * x + y * y - z * z


def cusp(x, y, z):
    """The cuspidal cubic y^2 z = x^3."""
    return y * y * z - x ** 3


def elliptic(x, y, z):
    """The elliptic curve y^2 z = x^3 - x z^2."""
    return y * y * z - x ** 3 + x * z * z


def trace_of_frobenius(p):
    """a_p = p + 1 - #E(F_p) for the elliptic curve y^2 = x^3 - x."""
    return p + 1 - count_points(elliptic, p)


def is_sum_of_two_squares_with(a, p):
    """True if p - a^2 is a perfect square (so p = a^2 + b^2)."""
    rest = p - a * a
    return rest >= 0 and math.isqrt(rest) ** 2 == rest


def main():
    primes = primes_between(3, 60)
    plane_ok = all(len(projective_points(p)) == p * p + p + 1
                   for p in primes)
    conic_ok = all(count_points(conic, p) == p + 1 for p in primes)
    cusp_ok = all(count_points(cusp, p) == p + 1 for p in primes)
    print(f"Primes 3 <= p < 60 ({len(primes)} primes):")
    print(f"  #P^2(F_p) = p^2 + p + 1:              {plane_ok}")
    print(f"  #conic x^2 + y^2 = z^2 equals p + 1:  {conic_ok}")
    print(f"  #cusp y^2 = x^3 equals p + 1:         {cusp_ok}")
    print("Elliptic curve E: y^2 = x^3 - x, a_p = p + 1 - #E(F_p):")
    rows = [(p, trace_of_frobenius(p)) for p in primes]
    for start in range(0, len(rows), 8):
        chunk = rows[start:start + 8]
        print("  " + "  ".join(f"p={p}:{a:+d}" for p, a in chunk))
    hasse = all(a * a <= 4 * p for p, a in rows)
    supersingular = all(a == 0 for p, a in rows if p % 4 == 3)
    gauss = all(a % 4 == 2 and is_sum_of_two_squares_with(a // 2, p)
                for p, a in rows if p % 4 == 1)
    print(f"  Hasse bound |a_p| <= 2 sqrt(p):       {hasse}")
    print(f"  a_p = 0 whenever p = 3 (mod 4):       {supersingular}")
    print(f"  p = 1 (mod 4): p = (a_p/2)^2 + b^2:   {gauss}")
    print()
    print("Epistemic status: exhaustive, exact counts for the primes listed.")
    print("They illustrate theorems proved elsewhere (the conic is P^1;")
    print("Hasse's bound; Deuring's theorem on supersingular primes) but")
    print("prove nothing about other primes.")


if __name__ == "__main__":
    main()
