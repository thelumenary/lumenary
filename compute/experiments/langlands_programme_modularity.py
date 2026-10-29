"""Modularity in action: an elliptic curve, a modular form, and Ramanujan's tau.

1. The elliptic curve 11a1: y^2 + y = x^3 - x^2 - 10x - 20 has a_p = p - (number
   of affine points mod p). The modular form
       f = q prod_{n>=1} (1 - q^n)^2 (1 - q^(11n))^2 = sum a_n q^n
   (weight 2, level 11) has the same a_p for every prime p - an instance of
   the modularity theorem (here classical: Eichler and Shimura). We check
   this exactly for p < 400.
2. Hecke theory predicts that the coefficients of f are multiplicative and
   satisfy a_(p^2) = a_p^2 - p for p != 11. We check this for n <= 400.
3. Ramanujan's Delta = q prod (1 - q^n)^24 = sum tau(n) q^n: multiplicativity
   (Mordell 1917), Ramanujan's congruence tau(n) = sigma_11(n) mod 691, and
   Deligne's bound |tau(p)| <= 2 p^(11/2) (1974), checked for n <= 400.
"""

import math

EXPERIMENT = {
    "id": "langlands_programme_modularity",
    "title": "An elliptic curve and its modular form; Ramanujan's tau",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["langlands-programme"],
    "summary": (
        "Counts points of the elliptic curve 11a1 modulo every prime p < 400 and "
        "compares the traces a_p with the coefficients of q prod (1 - q^n)^2 "
        "(1 - q^11n)^2; checks Hecke multiplicativity of those coefficients and "
        "of Ramanujan's tau(n), Ramanujan's congruence mod 691 and Deligne's "
        "bound, all for n <= 400. Exact finite checks of known theorems."
    ),
    "packages": [],
}

N = 400


def primes_below(n):
    """All primes p < n."""
    sieve = bytearray([1]) * max(n, 2)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, n, i)))
    return [i for i in range(n) if sieve[i]]


def series_mul(a, b, n):
    """Product of two power series (coefficient lists), truncated to degree < n."""
    out = [0] * n
    for i, ai in enumerate(a[:n]):
        if ai:
            for j, bj in enumerate(b[:n - i]):
                out[i + j] += ai * bj
    return out


def euler_product(n, m=1):
    """Coefficients of prod_{k>=1} (1 - q^(m k)) up to degree < n."""
    c = [0] * n
    c[0] = 1
    for k in range(1, (n - 1) // m + 1):
        step = m * k
        for j in range(n - 1, step - 1, -1):
            c[j] -= c[j - step]
    return c


def form_11a():
    """a[0..N] for q prod (1 - q^n)^2 (1 - q^(11n))^2 (a[0] = 0)."""
    e1, e11 = euler_product(N), euler_product(N, 11)
    c = series_mul(series_mul(e1, e1, N), series_mul(e11, e11, N), N)
    return [0] + c


def ramanujan_tau():
    """tau[0..N] for Delta = q prod (1 - q^n)^24 (tau[0] = 0)."""
    e = euler_product(N)
    e2 = series_mul(e, e, N)
    e3 = series_mul(e2, e, N)
    e6 = series_mul(e3, e3, N)
    e12 = series_mul(e6, e6, N)
    return [0] + series_mul(e12, e12, N)


def curve_trace(p):
    """a_p of 11a1: y^2 + y = x^3 - x^2 - 10x - 20, as p - #affine points."""
    if p == 2:
        affine = sum(1 for x in range(2) for y in range(2)
                     if (y * y + y - (x ** 3 - x * x - 10 * x - 20)) % 2 == 0)
        return p - affine
    # (2y + 1)^2 = 4(x^3 - x^2 - 10x - 20) + 1: count square roots
    roots = [0] * p
    for y in range(p):
        roots[y * y % p] += 1
    affine = sum(roots[(4 * (x ** 3 - x * x - 10 * x - 20) + 1) % p]
                 for x in range(p))
    return p - affine


def multiplicativity_failures(a, n):
    """Coprime pairs (m, k) with m * k <= n and a[m k] != a[m] a[k]."""
    return [(m, k) for m in range(2, n + 1) for k in range(m + 1, n // m + 1)
            if math.gcd(m, k) == 1 and a[m * k] != a[m] * a[k]]


def sigma(n, k):
    """Sum of the k-th powers of the divisors of n."""
    return sum(d ** k for d in range(1, n + 1) if n % d == 0)


def main():
    primes = primes_below(N)
    a = form_11a()
    terms = " ".join(f"{a[n]:+d}q^{n}" for n in range(1, 7))
    print("1. f = q prod (1 - q^n)^2 (1 - q^11n)^2")
    print("     = " + terms + " ...")
    match = sum(1 for p in primes if curve_trace(p) == a[p])
    print(f"   a_p(11a1) = a_p(f) for {match} of the {len(primes)} primes p < {N}")
    print()
    bad = multiplicativity_failures(a, N)
    square_law = all(a[p * p] == a[p] ** 2 - p for p in primes
                     if p * p <= N and p != 11)
    print(f"2. Hecke relations for f, n <= {N}: a_mn = a_m a_n (coprime): "
          f"{len(bad)} failures;")
    print(f"   a_(p^2) = a_p^2 - p for p != 11: {square_law}; "
          f"a_121 = a_11^2 = {a[121]}")
    print()
    tau = ramanujan_tau()
    print(f"3. Ramanujan: tau(1..6) = {tau[1:7]}")
    print(f"   multiplicativity failures (n <= {N}): "
          f"{len(multiplicativity_failures(tau, N))}")
    cong = all((tau[n] - sigma(n, 11)) % 691 == 0 for n in range(1, N + 1))
    print(f"   tau(n) = sigma_11(n) mod 691 for all n <= {N}: {cong}")
    ratio = max(abs(tau[p]) / (2 * p ** 5.5) for p in primes)
    print(f"   Deligne: max |tau(p)| / (2 p^(11/2)) over p < {N} = {ratio:.4f}")
    print()
    print("Epistemic status: exact integer arithmetic. Every check is a finite")
    print("verification of a theorem (modularity of 11a1, Hecke theory, Mordell,")
    print("Ramanujan's congruence, Deligne's bound); agreement for n <= 400")
    print("illustrates these theorems but proves nothing beyond the range tested.")


if __name__ == "__main__":
    main()
