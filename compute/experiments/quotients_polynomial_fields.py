"""Building finite fields as quotients F_p[x]/(f), and watching some fail.

Elements of F_p[x]/(f), for f of degree n, are the p^n polynomials of degree
below n, multiplied by reducing modulo f. The program checks, exhaustively,
whether every non-zero element has an inverse (so the quotient is a field) and
whether f has a root or factors, and confirms in each case: field exactly when f
is irreducible. For the fields it finds an element whose powers give every
non-zero element (the multiplicative group is cyclic), and it checks the
Chinese remainder isomorphism Z/12 = Z/3 x Z/4 against Z/4 versus Z/2 x Z/2.
"""

from itertools import product

EXPERIMENT = {
    "id": "quotients_polynomial_fields",
    "title": "Finite fields as quotient rings F_p[x]/(f)",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["quotients"],
    "summary": (
        "Constructs F_p[x]/(f) for several small p and f, tests every element for "
        "an inverse, and confirms that the quotient is a field exactly when f is "
        "irreducible (F4, F8, F9, F16 succeed; F2[x]/(x^2+1) and F3[x]/(x^2+x+1) "
        "fail). Finds generators of the multiplicative groups and checks the "
        "Chinese remainder theorem for Z/12. Exhaustive for these cases only."
    ),
    "packages": [],
}


def poly_mulmod(a, b, f, p):
    """Multiply coefficient lists a, b (lowest degree first) modulo f and p.

    f is monic of degree n; the result has length n."""
    n = len(f) - 1
    prod = [0] * (2 * n)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            prod[i + j] = (prod[i + j] + x * y) % p
    for k in range(2 * n - 1, n - 1, -1):      # reduce using x^n = -(lower terms)
        c = prod[k]
        if c:
            for t in range(n + 1):
                prod[k - n + t] = (prod[k - n + t] - c * f[t]) % p
    return tuple(prod[:n])


def elements(p, n):
    """All p^n residues: coefficient tuples of length n."""
    return [tuple(c) for c in product(range(p), repeat=n)]


def units(f, p):
    """Residues with a multiplicative inverse modulo f."""
    n = len(f) - 1
    one = tuple([1] + [0] * (n - 1))
    elems = elements(p, n)
    return [a for a in elems if any(poly_mulmod(a, b, f, p) == one for b in elems)]


def has_root(f, p):
    """True when f has a root in F_p."""
    return any(sum(c * pow(x, k, p) for k, c in enumerate(f)) % p == 0
               for x in range(p))


def is_irreducible(f, p):
    """Exhaustive: f (monic, degree n) has no monic factor of degree 1..n//2."""
    n = len(f) - 1
    for d in range(1, n // 2 + 1):
        for tail in product(range(p), repeat=d):
            g = list(tail) + [1]
            # long division of f by g over F_p
            r = list(f)
            for k in range(n - d, -1, -1):
                c = r[k + d]
                for t in range(d + 1):
                    r[k + t] = (r[k + t] - c * g[t]) % p
            if not any(r[:d]):
                return False
    return True


def generator(f, p):
    """A residue whose powers run through all non-zero residues, or None."""
    n = len(f) - 1
    one = tuple([1] + [0] * (n - 1))
    size = p ** n - 1
    for g in elements(p, n):
        if not any(g):
            continue
        power, k = g, 1
        while power != one and k <= size:
            power, k = poly_mulmod(power, g, f, p), k + 1
        if k == size:
            return g
    return None


def show_poly(f):
    """Coefficients listed lowest degree first, as text: [1, 1, 0, 1] -> x^3+x+1."""
    terms = []
    for k in range(len(f) - 1, -1, -1):
        c = f[k]
        if not c:
            continue
        mono = "" if k == 0 else ("x" if k == 1 else f"x^{k}")
        coef = str(c) if (c != 1 or k == 0) else ""
        terms.append(coef + mono)
    return "+".join(terms) if terms else "0"


def crt_is_isomorphism(m, n):
    """x -> (x mod m, x mod n) is a bijective ring map Z/mn -> Z/m x Z/n."""
    images = {(x % m, x % n) for x in range(m * n)}
    mult = all(((x * y) % m, (x * y) % n) == ((x % m) * (y % m) % m,
                                              (x % n) * (y % n) % n)
               for x in range(m * n) for y in range(m * n))
    return len(images) == m * n and mult


CASES = [(2, [1, 1, 1]), (2, [1, 0, 1]), (3, [1, 0, 1]), (3, [1, 1, 1]),
         (2, [1, 1, 0, 1]), (2, [1, 1, 0, 0, 1]), (5, [2, 0, 1])]


def main():
    print(" p  f            irreducible  root  units / non-zero  field  generator")
    for p, f in CASES:
        n = len(f) - 1
        u = units(f, p)
        field = len(u) == p ** n - 1
        g = generator(f, p) if field else None
        print(f"{p:>2}  {show_poly(f):<12} {str(is_irreducible(f, p)):<12} "
              f"{str(has_root(f, p)):<5} {len(u):>5} / {p ** n - 1:<9} "
              f"{str(field):<6} {show_poly(g) if g else '-'}")
    print("Field <=> f irreducible in every case:",
          all((len(units(f, p)) == p ** (len(f) - 1) - 1) == is_irreducible(f, p)
              for p, f in CASES))
    print(f"CRT: Z/12 -> Z/3 x Z/4 is an isomorphism: {crt_is_isomorphism(3, 4)}")
    print(f"     Z/4 -> Z/2 x Z/2 is an isomorphism: {crt_is_isomorphism(2, 2)}")
    print()
    print("Epistemic status: exact and exhaustive for the seven quotients and")
    print("the two maps shown. That k[x]/(f) is a field exactly when f is")
    print("irreducible, and that the unit group of a finite field is cyclic,")
    print("are theorems; these computations illustrate them, they do not prove")
    print("them.")


if __name__ == "__main__":
    main()
