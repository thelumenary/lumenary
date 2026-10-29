"""How rational primes split in quadratic fields, and the class group at work.

For K = Q(sqrt d) the ring of integers is Z[w] with w = sqrt d (d = 2, 3 mod 4)
or w = (1 + sqrt d)/2 (d = 1 mod 4), and the Dedekind-Kummer theorem says
that p splits, is inert or ramifies according as the minimal polynomial of w
has two, no or one (double) root modulo p. We compute this for every prime
p < 200 in four fields and compare with the prediction from the Kronecker
symbol (D/p) of the discriminant D. Then, in Q(sqrt -5), whose class number
is 2, we ask which split primes have *principal* prime factors: exactly those
with p = a^2 + 5b^2. They turn out to be the primes p = 1, 9 (mod 20), while
p = 3, 7 (mod 20) split into non-principal ideals - the class group made
visible. Exact and exhaustive for p < 200; the general statements are
theorems (Dedekind-Kummer; genus theory), not consequences of the check.
"""

import math

EXPERIMENT = {
    "id": "algebraic_number_theory_splitting",
    "title": "Splitting of primes in quadratic fields",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["algebraic-number-theory"],
    "summary": (
        "Factors every prime p < 200 in Q(i), Q(sqrt -5), Q(sqrt 2) and "
        "Q(sqrt 5) by counting roots of the minimal polynomial of the ring "
        "generator mod p (Dedekind-Kummer), checks agreement with the "
        "Kronecker symbol of the discriminant, and finds which split primes "
        "of Q(sqrt -5) have principal factors (p = a^2 + 5b^2). Exhaustive "
        "for p < 200 only."
    ),
    "packages": [],
}


def is_prime(n):
    """Trial division primality test."""
    return n >= 2 and all(n % q for q in range(2, math.isqrt(n) + 1))


def discriminant(d):
    """Discriminant of Q(sqrt d) for squarefree d != 0, 1."""
    return d if d % 4 == 1 else 4 * d


def min_poly(d):
    """Coefficients (b, c) of x^2 + b x + c, the minimal polynomial of w."""
    if d % 4 == 1:
        return (-1, (1 - d) // 4)
    return (0, -d)


def roots_mod_p(d, p):
    """Distinct roots modulo p of the minimal polynomial of w."""
    b, c = min_poly(d)
    return [x for x in range(p) if (x * x + b * x + c) % p == 0]


def splitting_type(d, p):
    """'split', 'inert' or 'ramified', by Dedekind-Kummer."""
    b, c = min_poly(d)
    roots = roots_mod_p(d, p)
    if len(roots) == 2:
        return "split"
    if not roots:
        return "inert"
    # one distinct root: check it is a double root (discriminant = 0 mod p)
    return "ramified" if (b * b - 4 * c) % p == 0 else "split"


def kronecker(a, p):
    """Kronecker symbol (a/p) for a prime p."""
    if p == 2:
        if a % 2 == 0:
            return 0
        return 1 if a % 8 in (1, 7) else -1
    r = pow(a % p, (p - 1) // 2, p)
    return 0 if a % p == 0 else (1 if r == 1 else -1)


PREDICTION = {1: "split", -1: "inert", 0: "ramified"}


def norm_form_represents(p, d):
    """True if p = a^2 + |d| b^2 for integers a, b (d < 0)."""
    return any(math.isqrt(p + d * b * b) ** 2 == p + d * b * b
               for b in range(math.isqrt(p // -d) + 1))


def main():
    primes = [p for p in range(2, 200) if is_prime(p)]
    print(f"Primes p < 200 ({len(primes)} primes), factored in O_K:")
    print(f"{'field':<10}{'D':>5}  split  inert  ramified  agrees with (D/p)")
    for d, name in [(-1, "Q(i)"), (-5, "Q(sqrt-5)"), (2, "Q(sqrt2)"),
                    (5, "Q(sqrt5)")]:
        D = discriminant(d)
        types = [splitting_type(d, p) for p in primes]
        agree = all(t == PREDICTION[kronecker(D, p)]
                    for t, p in zip(types, primes))
        counts = [types.count(t) for t in ("split", "inert", "ramified")]
        print(f"{name:<10}{D:>5}  {counts[0]:>5}  {counts[1]:>5}  "
              f"{counts[2]:>8}  {agree}")
    split = [p for p in primes if splitting_type(-5, p) == "split"]
    principal = [p for p in split if norm_form_represents(p, -5)]
    other = [p for p in split if p not in principal]
    print("Q(sqrt-5), class number 2: split primes p = P P'.")
    print(f"  P principal (p = a^2+5b^2): {principal[:9]} ...")
    print(f"  P not principal:            {other[:9]} ...")
    print("  residues mod 20, principal:",
          sorted({p % 20 for p in principal}),
          " not principal:", sorted({p % 20 for p in other}))
    print()
    print("Epistemic status: exact and exhaustive for primes below 200. The")
    print("agreement with (D/p) is the Dedekind-Kummer theorem; the residues")
    print("mod 20 illustrate genus theory. Neither is proved by this check.")


if __name__ == "__main__":
    main()
