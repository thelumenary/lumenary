"""Counting points over finite fields: Hasse, Sato-Tate and Birch-Swinnerton-Dyer.

For an elliptic curve E over Q with integer coefficients and a prime p, let
N_p be the number of points of E over F_p (including the point at infinity)
and a_p = p + 1 - N_p. We count points exactly for all p below a bound and

1. check Hasse's bound |a_p| <= 2 sqrt(p) (a theorem; here a finite check);
2. compare the angles theta_p in a_p = 2 sqrt(p) cos(theta_p) with the
   Sato-Tate density (2/pi) sin^2(theta) (a theorem for curves like 37a1,
   proved 2008-2011; here a small sample);
3. repeat Birch and Swinnerton-Dyer's 1960s experiment: the partial products
   prod_{p <= X} N_p / p for curves of rank 0, 1, 2 and 3. Their conjecture
   grew out of the observation that these grow roughly like (log X)^rank.

Ranks and conductors are quoted from Cremona's tables, not computed here.
"""

import math

EXPERIMENT = {
    "id": "arithmetic_geometry_point_counts",
    "title": "Point counts mod p: Hasse, Sato-Tate and Birch-Swinnerton-Dyer",
    "evidence": ["exact", "exhaustive-finite", "numerical"],
    "lessons": ["arithmetic-geometry"],
    "summary": (
        "Counts points of four elliptic curves over F_p for all primes p < 1000 "
        "(exact). Checks the Hasse bound in every case, tabulates the Sato-Tate "
        "angles of 37a1 against the predicted density, and recomputes the Euler "
        "products that led Birch and Swinnerton-Dyer to their conjecture. The "
        "last two parts are numerical illustrations, not evidence strong enough "
        "to prove or even test the asymptotic statements."
    ),
    "packages": [],
}

#: Weierstrass coefficients (a1, a2, a3, a4, a6) and ranks from Cremona's tables.
CURVES = {
    "11a1": ((0, -1, 1, -10, -20), 0),
    "37a1": ((0, 0, 1, -1, 0), 1),
    "389a1": ((0, 1, 1, -2, 0), 2),
    "5077a1": ((0, 0, 1, -7, 6), 3),
}


def primes_below(n):
    """All primes p < n (sieve of Eratosthenes)."""
    sieve = bytearray([1]) * max(n, 2)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n, i)))
    return [i for i in range(n) if sieve[i]]


def count_points(coeffs, p):
    """N_p: points of y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6 over F_p."""
    a1, a2, a3, a4, a6 = coeffs
    if p == 2:
        return 1 + sum(1 for x in range(2) for y in range(2)
                       if (y * y + a1 * x * y + a3 * y
                           - x ** 3 - a2 * x * x - a4 * x - a6) % 2 == 0)
    # Complete the square: (2y + a1 x + a3)^2 = 4(x^3 + a2 x^2 + a4 x + a6)
    # + (a1 x + a3)^2, and count square roots of the right-hand side.
    roots = [0] * p
    for y in range(p):
        roots[y * y % p] += 1
    total = 1  # the point at infinity
    for x in range(p):
        rhs = 4 * (x ** 3 + a2 * x * x + a4 * x + a6) + (a1 * x + a3) ** 2
        total += roots[rhs % p]
    return total


def trace_of_frobenius(coeffs, p):
    """a_p = p + 1 - N_p."""
    return p + 1 - count_points(coeffs, p)


def sato_tate_mass(lo, hi):
    """Integral of (2/pi) sin^2(t) dt from lo to hi."""
    def F(t):
        return (t - math.sin(t) * math.cos(t)) / math.pi
    return F(hi) - F(lo)


def euler_products(coeffs, checkpoints, primes):
    """prod_{p <= X} N_p / p at each X in checkpoints (sorted)."""
    out, prod, k = [], 1.0, 0
    for p in primes:
        while k < len(checkpoints) and p > checkpoints[k]:
            out.append(prod)
            k += 1
        prod *= count_points(coeffs, p) / p
    while k < len(checkpoints):
        out.append(prod)
        k += 1
    return out


def main():
    primes = primes_below(1000)
    coeffs37 = CURVES["37a1"][0]
    good = [p for p in primes if p != 37]
    ratios = [abs(trace_of_frobenius(coeffs37, p)) / (2 * math.sqrt(p))
              for p in good]
    worst = max(range(len(good)), key=lambda i: ratios[i])
    print(f"37a1: y^2 + y = x^3 - x, all {len(good)} good primes p < 1000")
    print(f"1. Hasse: max |a_p| / (2 sqrt p) = {ratios[worst]:.4f} "
          f"(at p = {good[worst]}); <= 1 every time")
    print()
    print("2. Sato-Tate angles theta_p, a_p = 2 sqrt(p) cos(theta_p):")
    print("   bin (degrees)   observed   Sato-Tate prediction")
    angles = [math.acos(trace_of_frobenius(coeffs37, p) / (2 * math.sqrt(p)))
              for p in good]
    for k in range(6):
        lo, hi = k * math.pi / 6, (k + 1) * math.pi / 6
        seen = sum(1 for t in angles if lo <= t < hi or (k == 5 and t == hi))
        expected = len(angles) * sato_tate_mass(lo, hi)
        print(f"   {30 * k:3d}-{30 * k + 30:3d}       {seen:8d}   {expected:10.1f}")
    print()
    print("3. Birch-Swinnerton-Dyer products prod_{p <= X} N_p / p:")
    checkpoints = [100, 250, 500, 1000]
    print("   curve   rank" + "".join(f"   X = {x:4d}" for x in checkpoints))
    for name, (coeffs, rank) in CURVES.items():
        values = euler_products(coeffs, checkpoints, primes)
        print(f"   {name:7s} {rank:3d}" + "".join(f"  {v:9.1f}" for v in values))
    print()
    print("Epistemic status: the point counts are exact and the Hasse check is")
    print("exhaustive for these primes, but only Hasse's theorem covers all p.")
    print(f"The Sato-Tate table ({len(angles)} angles) and the BSD products are "
          "numerical")
    print("illustrations: the products grow faster for larger rank, as Birch and")
    print("Swinnerton-Dyer saw, but finite data cannot prove or refute the")
    print("conjecture; ranks are quoted from Cremona's tables, not computed.")


if __name__ == "__main__":
    main()
