"""The p-adic integers as an inverse limit: compatible towers of residues.

A point of the inverse limit of ... -> Z/p^3 -> Z/p^2 -> Z/p is a sequence of
residues x_n mod p^n with x_(n+1) = x_n (mod p^n). We build such towers for -1
and 1/3 (a fraction with denominator prime to p), and for a square root of -1
in the 5-adic integers by Hensel lifting; we check compatibility and that the
ring operations work level by level. Counting the solutions of x^2 = a modulo
p^n shows how many points the limit has: two square roots of -1 in Z_5, none
of 2.
"""

EXPERIMENT = {
    "id": "limits_colimits_padic",
    "title": "The p-adic integers as compatible towers of residues",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["limits-colimits"],
    "summary": (
        "Builds compatible towers x_n mod p^n representing -1 and 1/3 in Z_2 and Z_5 "
        "and a square root of -1 in Z_5 (Hensel lifting), checks compatibility and "
        "levelwise arithmetic, and counts solutions of x^2 = -1 and x^2 = 2 modulo "
        "5^n for n <= 6. Exact for the levels computed; that the towers determine "
        "p-adic integers is the inverse-limit theorem."
    ),
    "packages": [],
}


def tower_of_fraction(num, den, p, levels):
    """Residues of num/den modulo p, p^2, ..., p^levels (den prime to p)."""
    if den % p == 0:
        raise ValueError("denominator must be prime to p")
    return [num * pow(den, -1, p ** n) % p ** n for n in range(1, levels + 1)]


def is_compatible(tower, p):
    """Does x_(n+1) reduce to x_n modulo p^n for every level n?"""
    return all(tower[n + 1] % p ** (n + 1) == tower[n] % p ** (n + 1)
               for n in range(len(tower) - 1))


def hensel_sqrt(a, p, x1, levels):
    """Lift a root x1 of x^2 = a (mod p), with 2 x1 invertible mod p, to a
    compatible tower of roots modulo p^n (Newton's method)."""
    if (x1 * x1 - a) % p or (2 * x1) % p == 0:
        raise ValueError("need x1^2 = a and 2 x1 != 0 modulo p")
    tower, x = [x1 % p], x1 % p
    for n in range(2, levels + 1):
        m = p ** n
        x = (x - (x * x - a) * pow(2 * x, -1, m)) % m
        tower.append(x)
    return tower


def roots_mod(a, m):
    """All x mod m with x^2 = a (mod m), by exhaustive search."""
    return [x for x in range(m) if (x * x - a) % m == 0]


def levelwise(op, s, t, p):
    """Apply a ring operation to two towers level by level."""
    return [op(x, y) % p ** (n + 1) for n, (x, y) in enumerate(zip(s, t))]


def main():
    minus_one = tower_of_fraction(-1, 1, 5, 6)
    third = tower_of_fraction(1, 3, 2, 8)
    i5 = hensel_sqrt(-1, 5, 2, 6)
    print("Towers x_n mod p^n (n = 1, 2, ...):")
    print(f"  -1  in Z_5: {minus_one}")
    print(f"  1/3 in Z_2: {third}")
    print(f"  sqrt(-1) in Z_5: {i5}")
    print("Compatible (x_(n+1) = x_n mod p^n): "
          f"{is_compatible(minus_one, 5)}, {is_compatible(third, 2)}, "
          f"{is_compatible(i5, 5)}")
    square = levelwise(lambda x, y: x * y, i5, i5, 5)
    three = [3 % 2 ** (n + 1) for n in range(8)]
    one = levelwise(lambda x, y: x * y, three, third, 2)
    print(f"Levelwise: sqrt(-1)^2 = -1 at every level: {square == minus_one}; "
          f"3 * (1/3) = 1: {set(one) == {1}}")
    fake = [n % 5 ** n for n in range(1, 7)]
    print(f"Not a point of the limit: x_n = n mod 5^n {fake[:4]}... compatible: "
          f"{is_compatible(fake, 5)}")
    print()
    print("Solutions modulo 5^n:   n = 1  2  3  4  5  6")
    for a in (-1, 2):
        counts = [len(roots_mod(a, 5 ** n)) for n in range(1, 7)]
        print(f"  x^2 = {a:>2}:              " + "  ".join(map(str, counts)))
    print("As Hensel's lemma predicts, each root mod 5^n lifts to exactly one root")
    print("mod 5^(n+1): Z_5 has two square roots of -1, and none of 2.")
    print()
    print("Epistemic status: exact modular arithmetic for the levels shown, with")
    print("an exhaustive count of roots up to 5^6. Finitely many levels never")
    print("pin down a p-adic integer; that compatible towers are exactly the points")
    print("of Z_p (and Hensel's lemma for all levels) is proved, not computed.")


if __name__ == "__main__":
    main()
