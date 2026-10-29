"""When can a polynomial have more roots than its degree?

Over the real or complex numbers a non-zero polynomial of degree n has at most
n roots. The proof uses the zero-product property: if uv = 0 then u = 0 or
v = 0. In clock arithmetic modulo n that property fails when n is composite,
and so does the root bound. This experiment counts roots of x^2 - 1 modulo n
and checks the bound exhaustively for every polynomial of degree at most 3
modulo the primes 2, 3, 5 and 7.
"""

from itertools import product

EXPERIMENT = {
    "id": "polynomials_roots_mod_n",
    "title": "More roots than the degree? Polynomials modulo n",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["polynomials"],
    "summary": (
        "Counts the roots of x^2 - 1 modulo n for n = 2..24 (n = 8 gives four "
        "roots of a quadratic), and checks exhaustively that every non-zero "
        "polynomial of degree at most 3 modulo 2, 3, 5 and 7 has at most "
        "degree-many roots, as the proof predicts when there are no zero divisors."
    ),
    "packages": [],
}


def roots_mod(coeffs, n):
    """Residues x in 0..n-1 with p(x) = 0 mod n; coefficients highest first."""
    found = []
    for x in range(n):
        value = 0
        for c in coeffs:
            value = (value * x + c) % n
        if value == 0:
            found.append(x)
    return found


def degree_mod(coeffs, p):
    """Degree of the polynomial modulo p, or None for the zero polynomial."""
    for i, c in enumerate(coeffs):
        if c % p:
            return len(coeffs) - 1 - i
    return None


def bound_violations(p, max_degree):
    """Count non-zero polynomials of degree <= max_degree mod p with more
    roots than their degree. Returns (number checked, violations)."""
    checked = violations = 0
    for coeffs in product(range(p), repeat=max_degree + 1):
        d = degree_mod(coeffs, p)
        if d is None:
            continue
        checked += 1
        violations += len(roots_mod(coeffs, p)) > d
    return checked, violations


def zero_divisors(n):
    """Pairs (u, v) with 0 < u <= v < n and u*v = 0 mod n."""
    return [(u, v) for u in range(1, n) for v in range(u, n) if u * v % n == 0]


def main():
    print("roots of x^2 - 1 modulo n (degree 2, so at most 2 if the bound held):")
    row = []
    for n in range(2, 25):
        row.append(f"{n}:{len(roots_mod([1, 0, -1], n))}")
        if len(row) == 8:
            print("  " + "  ".join(row))
            row = []
    if row:
        print("  " + "  ".join(row))
    print("  modulo 8 the roots are", roots_mod([1, 0, -1], 8),
          "- four roots of a quadratic")
    print("  why: (x - 1)(x + 1) = 0 mod 8 with neither factor 0,")
    print("  e.g. x = 3 gives 2 * 4 = 8; zero divisors mod 8:", zero_divisors(8))
    print()
    print("every non-zero polynomial of degree <= 3 modulo a prime p:")
    for p in (2, 3, 5, 7):
        checked, bad = bound_violations(p, 3)
        print(f"  p = {p}: {checked:5d} polynomials, {bad} with too many roots")
    print()
    print("Epistemic status: every count above is an exact, exhaustive check of")
    print("finitely many cases, and the modulo-8 example is a genuine")
    print("counterexample showing the zero-product hypothesis is needed. The")
    print("checks prove nothing about higher degrees or other primes; the")
    print("lesson's proof covers every integral domain.")


if __name__ == "__main__":
    main()
