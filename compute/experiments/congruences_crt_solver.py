"""Solving congruences: inverses, linear congruences and the Chinese remainder theorem.

The extended Euclidean algorithm writes gcd(a, n) = ua + vn. From it the
experiment computes inverses modulo n, solves linear congruences ax = b
(mod n) - which have gcd(a, n) solutions or none - and combines congruences
with the Chinese remainder theorem, starting with the remainder problem from
the Sunzi Suanjing. It then checks by brute force that x -> (x mod 3, x mod 5,
x mod 7) is a bijection from Z/105Z onto Z/3Z x Z/5Z x Z/7Z, and that two
congruences with non-coprime moduli can be inconsistent. The answers are
exact; the bijection check is exhaustive for this one modulus.
"""

import math

EXPERIMENT = {
    "id": "congruences_crt_solver",
    "title": "Inverses, linear congruences and the Chinese remainder theorem",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["congruences"],
    "summary": (
        "Uses the extended Euclidean algorithm to find inverses modulo n, to "
        "solve linear congruences ax = b (mod n) (gcd(a, n) solutions or none) "
        "and to solve systems by the Chinese remainder theorem, including Sunzi's "
        "problem. Checks exhaustively that Z/105Z -> Z/3 x Z/5 x Z/7 is a bijection "
        "and that non-coprime moduli can be inconsistent."
    ),
    "packages": [],
}


def ext_gcd(a, b):
    """Return (g, u, v) with g = gcd(a, b) = u*a + v*b and g >= 0."""
    old_r, r, old_u, u, old_v, v = a, b, 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_u, u = u, old_u - q * u
        old_v, v = v, old_v - q * v
    if old_r < 0:
        old_r, old_u, old_v = -old_r, -old_u, -old_v
    return old_r, old_u, old_v


def inverse_mod(a, n):
    """The inverse of a modulo n in range(n), or None if gcd(a, n) != 1."""
    g, u, _ = ext_gcd(a, n)
    return u % n if g == 1 else None


def solve_linear(a, b, n):
    """All x in range(n) with a*x = b (mod n), found from the gcd."""
    g, u, _ = ext_gcd(a, n)
    if b % g:
        return []
    x0 = (u * (b // g)) % (n // g)
    return [x0 + k * (n // g) for k in range(g)]


def crt(residues, moduli):
    """Solve x = r_i (mod m_i) for pairwise coprime m_i; return (x, M)."""
    x, m = 0, 1
    for r, n in zip(residues, moduli):
        g, u, v = ext_gcd(m, n)
        if g != 1:
            raise ValueError("moduli must be pairwise coprime")
        # u*m + v*n = 1, so x*v*n + r*u*m is x mod m and r mod n.
        x = (x * v * n + r * u * m) % (m * n)
        m *= n
    return x, m


def crt_is_bijection(moduli):
    """True if x -> (x mod m_1, ...) hits every tuple exactly once."""
    big = math.prod(moduli)
    images = {tuple(x % n for n in moduli) for x in range(big)}
    return len(images) == big


def consistent(r1, m1, r2, m2):
    """Brute force: is there an x with x = r1 (mod m1) and x = r2 (mod m2)?"""
    return any(x % m1 == r1 % m1 and x % m2 == r2 % m2
               for x in range(m1 * m2))


def main():
    g, u, v = ext_gcd(240, 46)
    print(f"Bezout: gcd(240, 46) = {g} = ({u})*240 + ({v})*46")
    for a, n in [(7, 26), (17, 43), (6, 9)]:
        print(f"inverse of {a} mod {n}: {inverse_mod(a, n)}")
    for a, b, n in [(6, 4, 10), (6, 5, 10), (5, 3, 7)]:
        print(f"{a}x = {b} (mod {n}): x in {solve_linear(a, b, n)}")
    print()
    x, m = crt([2, 3, 2], [3, 5, 7])
    print("Sunzi: x = 2 (mod 3), x = 3 (mod 5), x = 2 (mod 7)")
    print(f"  x = {x} (mod {m})")
    x, m = crt([2, 3, 4], [5, 7, 9])
    print(f"x = 2 (mod 5), 3 (mod 7), 4 (mod 9): x = {x} (mod {m})")
    print(f"Z/105 -> Z/3 x Z/5 x Z/7 bijective: {crt_is_bijection([3, 5, 7])}")
    print(f"Z/24 -> Z/4 x Z/6 bijective:         {crt_is_bijection([4, 6])}")
    print("x = 1 (mod 4) and x = 2 (mod 6) solvable:", consistent(1, 4, 2, 6))
    print("x = 1 (mod 4) and x = 3 (mod 6) solvable:", consistent(1, 4, 3, 6))
    print()
    print("Epistemic status: every answer is exact and can be checked by")
    print("substituting it back; the bijection and consistency checks are")
    print("exhaustive for these moduli only. That the method always works is")
    print("the content of Bezout's identity and the Chinese remainder theorem.")


if __name__ == "__main__":
    main()
