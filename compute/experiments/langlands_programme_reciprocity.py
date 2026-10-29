"""Reciprocity laws: when does a polynomial factor modulo p?

For a polynomial f with integer coefficients, how f factors modulo a prime p
is governed by the Frobenius element at p in the Galois group of f.

1. Quadratic reciprocity, checked for every pair of distinct odd primes below
   200 with Euler's criterion.
2. Abelian splitting laws: x^2 + 1 has roots mod p exactly when p = 1 mod 4,
   and x^2 - 5 exactly when p = +-1 mod 5. Congruences decide everything.
3. A non-abelian splitting law: the number of roots of x^3 - x - 1 mod p is
   NOT determined by any congruence on p (we exhibit primes in the same
   class mod 23 that behave differently), but it IS given by the coefficients
   of the modular form eta(z) eta(23z) = q prod (1 - q^n)(1 - q^(23n)):
   #roots = a_p + 1 for p != 23. This is a theorem (Hecke's theory of theta
   series for Q(sqrt(-23))); here we check it for p < 2000.
4. Chebotarev statistics for x^3 - x - 1, whose Galois group is S_3: the
   proportions of primes with 3, 1 and 0 roots approach 1/6, 1/2, 1/3.
"""

EXPERIMENT = {
    "id": "langlands_programme_reciprocity",
    "title": "Reciprocity laws: quadratic, cyclotomic and a modular form",
    "evidence": ["exact", "exhaustive-finite", "statistical"],
    "lessons": ["langlands-programme"],
    "summary": (
        "Checks quadratic reciprocity for all pairs of odd primes below 200, "
        "verifies the congruence splitting laws of x^2 + 1 and x^2 - 5, shows that "
        "no congruence mod 23 decides how x^3 - x - 1 factors while the modular "
        "form eta(z)eta(23z) does (all p < 2000), and compares splitting "
        "frequencies with Chebotarev's densities. Finite checks of theorems."
    ),
    "packages": [],
}


def primes_below(n):
    """All primes p < n."""
    sieve = bytearray([1]) * max(n, 2)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n, i)))
    return [i for i in range(n) if sieve[i]]


def legendre(a, p):
    """The Legendre symbol (a/p) for an odd prime p, by Euler's criterion."""
    r = pow(a % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def reciprocity_failures(primes):
    """Pairs p < q of odd primes violating (p/q)(q/p) = (-1)^((p-1)(q-1)/4)."""
    odd = [p for p in primes if p > 2]
    bad = []
    for i, p in enumerate(odd):
        for q in odd[i + 1:]:
            sign = (-1) ** (((p - 1) // 2) * ((q - 1) // 2))
            if legendre(p, q) * legendre(q, p) != sign:
                bad.append((p, q))
    return bad


def root_count(coeffs, p):
    """Number of roots mod p of the polynomial with coefficients (highest first)."""
    count = 0
    for x in range(p):
        v = 0
        for c in coeffs:
            v = (v * x + c) % p
        count += v == 0
    return count


def eta_product_coefficients(N, levels):
    """a_1..a_N of q * prod_n prod_{m in levels} (1 - q^(m n)), as a list a[0..N]."""
    c = [0] * N  # c[k] = coefficient of q^k in the product (without the q)
    c[0] = 1
    for m in levels:
        for n in range(1, N // m + 1):
            step = m * n
            for k in range(N - 1, step - 1, -1):
                c[k] -= c[k - step]
    return [0] + c  # a[n] = c[n - 1]


def main():
    primes = primes_below(2000)
    pairs = len([p for p in primes if 2 < p < 200])
    bad = reciprocity_failures([p for p in primes if p < 200])
    print(f"1. Quadratic reciprocity: {pairs * (pairs - 1) // 2} pairs of odd "
          f"primes < 200, {len(bad)} failures")
    print()
    odd = [p for p in primes if p > 5]
    law1 = all((root_count([1, 0, 1], p) == 2) == (p % 4 == 1) for p in odd)
    law2 = all((root_count([1, 0, -5], p) == 2) == (p % 5 in (1, 4)) for p in odd)
    print(f"2. For all {len(odd)} primes 5 < p < 2000:")
    print(f"   x^2 + 1 has roots mod p  <=>  p = 1 mod 4      : {law1}")
    print(f"   x^2 - 5 has roots mod p  <=>  p = +-1 mod 5    : {law2}")
    print()
    cubic = [1, 0, -1, -1]
    counts = {p: root_count(cubic, p) for p in primes}
    seen, clash = {}, None
    for p in primes:
        if p != 23:
            r = p % 23
            if r in seen and counts[seen[r]] != counts[p] and clash is None:
                clash = (seen[r], p)
            seen.setdefault(r, p)
    p0, p1 = clash
    print("3. x^3 - x - 1 (discriminant -23):")
    print(f"   p = {p0} and p = {p1} are both {p0 % 23} mod 23, but have "
          f"{counts[p0]} and {counts[p1]} roots:")
    print("   no congruence condition decides how the cubic factors.")
    a = eta_product_coefficients(2000, [1, 23])
    agree = sum(1 for p in primes if p != 23 and counts[p] == a[p] + 1)
    print(f"   eta(z)eta(23z) = q - q^2 - q^3 + q^6 + q^8 - ...: "
          f"a_p + 1 = #roots")
    print(f"   for {agree} of the {len(primes) - 1} primes p < 2000, p != 23")
    print()
    good = [p for p in primes if p != 23]
    print("4. Chebotarev for Gal = S_3, primes p < 2000:")
    for k, name, density in [(3, "3 roots (identity)", "1/6"),
                             (1, "1 root (transposition)", "1/2"),
                             (0, "0 roots (3-cycle)", "1/3")]:
        share = sum(1 for p in good if counts[p] == k) / len(good)
        print(f"   {name:24s}: {share:.3f}  (density {density})")
    print()
    print("Epistemic status: parts 1-3 are exact, exhaustive checks over finite")
    print("ranges of theorems (quadratic reciprocity; the splitting laws; the")
    print("modularity of the S_3 representation, a classical theorem of Hecke).")
    print("They prove nothing beyond the primes tested. Part 4 is statistical:")
    print("Chebotarev's theorem gives the limiting densities, not finite counts.")


if __name__ == "__main__":
    main()
