"""Quadratic reciprocity, checked three ways, and sums of two squares.

For every pair of distinct odd primes p, q below 200 the program computes the
Legendre symbols (p/q) and (q/p) by Euler's criterion and checks the law of
quadratic reciprocity. It also checks the two ingredients of the lesson's proof:
Gauss's lemma, (q/p) = (-1)^mu with mu the number of "negative" least residues
of q, 2q, ..., ((p-1)/2) q, and Eisenstein's lattice-point identity, that the
points under the diagonal of the (p/2) x (q/2) rectangle number
((p-1)/2)((q-1)/2). Finally it lists which primes are sums of two squares.
"""

EXPERIMENT = {
    "id": "elementary_number_theory_reciprocity",
    "title": "Quadratic reciprocity and sums of two squares by computer",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["elementary-number-theory"],
    "summary": (
        "Checks quadratic reciprocity, Gauss's lemma and Eisenstein's lattice-point "
        "count for all pairs of distinct odd primes below 200, verifies the "
        "supplementary laws for -1 and 2, and finds which primes below 100 are sums "
        "of two squares (exactly 2 and those = 1 mod 4). Exhaustive for these "
        "ranges; the proofs for all primes are in the lesson."
    ),
    "packages": [],
}


def odd_primes_below(n):
    """Odd primes below n by trial division."""
    return [p for p in range(3, n, 2) if all(p % d for d in range(3, int(p ** 0.5) + 1, 2))]


def legendre(a, p):
    """Legendre symbol (a/p) for an odd prime p, by Euler's criterion."""
    r = pow(a % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def gauss_lemma(q, p):
    """(-1)^mu, mu = number of k*q (1 <= k <= (p-1)/2) with residue above p/2."""
    mu = sum((k * q) % p > p // 2 for k in range(1, (p - 1) // 2 + 1))
    return (-1) ** mu


def lattice_points(p, q):
    """Points (x, y), 1 <= x <= (p-1)/2, 1 <= y <= (q-1)/2, counted in two
    triangles: below the diagonal qx = py, and above it."""
    below = sum((k * q) // p for k in range(1, (p - 1) // 2 + 1))
    above = sum((k * p) // q for k in range(1, (q - 1) // 2 + 1))
    return below, above


def two_squares(n):
    """A representation n = a^2 + b^2 with 0 <= a <= b, or None."""
    a = 0
    while 2 * a * a <= n:
        b2 = n - a * a
        b = int(round(b2 ** 0.5))
        for c in (b - 1, b, b + 1):
            if c >= 0 and c * c == b2:
                return a, c
        a += 1
    return None


def main():
    primes = odd_primes_below(200)
    pairs = [(p, q) for p in primes for q in primes if p < q]
    reciprocity = all(legendre(p, q) * legendre(q, p)
                      == (-1) ** (((p - 1) // 2) * ((q - 1) // 2)) for p, q in pairs)
    gauss = all(gauss_lemma(q, p) == legendre(q, p) for p, q in pairs) and all(
        gauss_lemma(p, q) == legendre(p, q) for p, q in pairs)
    eisenstein = all(sum(lattice_points(p, q)) == ((p - 1) // 2) * ((q - 1) // 2)
                     for p, q in pairs)
    print(f"{len(pairs)} pairs of distinct odd primes below 200:")
    print(f"  (p/q)(q/p) = (-1)^((p-1)/2 * (q-1)/2) in every case: {reciprocity}")
    print(f"  Gauss's lemma agrees with Euler's criterion:         {gauss}")
    print(f"  lattice points below + above diagonal = product:     {eisenstein}")
    below, above = lattice_points(7, 11)
    print(f"  e.g. p = 7, q = 11: {below} + {above} = {below + above} = 3 * 5;"
          f" (7/11)(11/7) = {legendre(7, 11) * legendre(11, 7)}")
    minus_one = all((legendre(-1, p) == 1) == (p % 4 == 1) for p in primes)
    two = all((legendre(2, p) == 1) == (p % 8 in (1, 7)) for p in primes)
    print(f"  (-1/p) = 1 exactly when p = 1 mod 4:  {minus_one}")
    print(f"  (2/p) = 1 exactly when p = +-1 mod 8: {two}")
    print("Primes below 100 as sums of two squares:")
    reps = [(p, two_squares(p)) for p in [2] + odd_primes_below(100)]
    line = ""
    for p, rep in reps:
        if rep:
            item = f"{p}={rep[0]}^2+{rep[1]}^2"
            if len(line) + len(item) > 74:
                print("  " + line.rstrip())
                line = ""
            line += item + "  "
    print("  " + line.rstrip())
    missing = [p for p, rep in reps if rep is None]
    print(f"  not sums of two squares: {missing}")
    print(f"  all of these are 3 mod 4: {all(p % 4 == 3 for p in missing)}")
    print()
    print("Epistemic status: exact, exhaustive checks for primes below 200 (and")
    print("100). They confirm the theorems for these primes only; the lesson's")
    print("proofs (Gauss's lemma and Eisenstein's count, and the Gaussian")
    print("integers for two squares) cover all primes.")


if __name__ == "__main__":
    main()
