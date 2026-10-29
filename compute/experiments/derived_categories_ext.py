"""Ext groups from resolutions, and Ext^1 from extensions, by exact counting.

In the derived category, Ext^n(M, N) = Hom(M, N[n]). To compute it we replace
M by a projective resolution P -> M (a quasi-isomorphism) and take cohomology
of the complex Hom(P, N). Here every module is a finite cyclic group, so
kernels and images can be counted element by element. Over Z every module
has a resolution of length 1 and Ext^n vanishes for n >= 2; over Z/4 the
module Z/2 has an infinite periodic resolution and Ext^n(Z/2, Z/2) = Z/2 for
every n, while Z/4 is injective over itself. Finally we count the extensions
0 -> Z/p -> E -> Z/p -> 0 directly, as symmetric 2-cocycles modulo
coboundaries, and find p classes: |Ext^1(Z/p, Z/p)| = p, with one split
class and p - 1 classes in which E is cyclic. Exact, exhaustive-finite
evidence for the cases shown; the general theorems are proved in the lesson
and its references.
"""

from itertools import product
from math import gcd

EXPERIMENT = {
    "id": "derived_categories_ext",
    "title": "Ext from resolutions and from extensions",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["derived-categories"],
    "summary": (
        "Computes Ext^n(M, N) for finite cyclic modules over Z and over Z/N as "
        "cohomology of Hom(P, N) for explicit projective resolutions P, by "
        "counting kernels and images element by element; then counts extensions "
        "of Z/p by Z/p as symmetric 2-cocycles modulo coboundaries for p = 2, 3. "
        "Exact for these small cases, which illustrate Ext^n = Hom_D(M, N[n])."
    ),
    "packages": [],
}


def mult_kernel_image(b, c):
    """Sizes of kernel and image of x -> c x on Z/b (by enumeration)."""
    image = {(c * x) % b for x in range(b)}
    kernel = [x for x in range(b) if (c * x) % b == 0]
    return len(kernel), len(image)


def cohomology_orders(b, factors):
    """Orders of H^n of Z/b --c0--> Z/b --c1--> ... --c_{k-1}--> Z/b.

    The complex has len(factors) + 1 terms; H^n = ker d^n / im d^(n-1), with
    d^n = 0 past the last term.
    """
    orders = []
    for n in range(len(factors) + 1):
        ker = mult_kernel_image(b, factors[n])[0] if n < len(factors) else b
        im = mult_kernel_image(b, factors[n - 1])[1] if n > 0 else 1
        orders.append(ker // im)
    return orders


def ext_over_z(a, b, top=3):
    """|Ext^n_Z(Z/a, Z/b)|, n = 0..top, from 0 -> Z --a--> Z -> Z/a."""
    orders = cohomology_orders(b, [a])  # Hom(P0, N) --a--> Hom(P1, N)
    return (orders + [1] * (top + 1))[: top + 1]


def ext_over_zn(big_n, a, b, top=5):
    """|Ext^n_{Z/N}(Z/a, Z/b)| for a, b dividing N, n = 0..top.

    Periodic resolution ... -> Z/N --a--> Z/N --N/a--> Z/N --a--> Z/N -> Z/a.
    Hom(Z/N, Z/b) = Z/b, and the induced maps are the same multiplications.
    """
    if big_n % a or big_n % b:
        raise ValueError("a and b must divide N")
    factors = [a if n % 2 == 0 else big_n // a for n in range(top + 1)]
    return cohomology_orders(b, factors)[: top + 1]


def homs(a, b):
    """Number of group homomorphisms Z/a -> Z/b (brute force)."""
    return sum(1 for x in range(b) if (a * x) % b == 0)


def extension_classes(p):
    """Classes of extensions 0 -> Z/p -> E -> Z/p -> 0 via 2-cocycles.

    Returns (number of classes, number of classes with E cyclic). A symmetric
    normalised cocycle f gives E = Z/p x Z/p with
    (n, a) + (m, b) = (n + m + f(a, b), a + b); cohomologous cocycles give
    equivalent extensions.
    """
    pairs = list(product(range(p), repeat=2))
    cocycles = []
    for values in product(range(p), repeat=len(pairs)):
        f = dict(zip(pairs, values))
        if f[(0, 0)] or any(f[(a, b)] != f[(b, a)] for a, b in pairs):
            continue
        if all((f[(b, c)] - f[((a + b) % p, c)] + f[(a, (b + c) % p)]
                - f[(a, b)]) % p == 0
               for a, b, c in product(range(p), repeat=3)):
            cocycles.append(f)
    boundaries = set()
    for g in product(range(p), repeat=p):
        if g[0] == 0:
            boundaries.add(tuple((g[a] + g[b] - g[(a + b) % p]) % p
                                 for a, b in pairs))
    classes = {}
    for f in cocycles:
        key = min(tuple((f[q] - d[i]) % p for i, q in enumerate(pairs))
                  for d in boundaries)
        classes[key] = f
    cyclic = sum(1 for f in classes.values() if extension_is_cyclic(f, p))
    return len(classes), cyclic


def extension_is_cyclic(f, p):
    """Is the group E built from the cocycle f cyclic (an element of order p^2)?"""
    for n0, a0 in product(range(p), repeat=2):
        n, a, order = n0, a0, 1
        while (n, a) != (0, 0):
            n, a = (n + n0 + f[(a, a0)]) % p, (a + a0) % p
            order += 1
        if order == p * p:
            return True
    return False


def main():
    print("Ext over Z (resolution 0 -> Z --a--> Z -> Z/a):")
    for a, b in [(2, 2), (4, 6), (3, 5)]:
        print(f"  |Ext^n(Z/{a}, Z/{b})|, n = 0..3: {ext_over_z(a, b)}"
              f"   |Hom| = {homs(a, b)} = gcd = {gcd(a, b)}")
    print("Ext over Z/4 (periodic resolution ... --2--> Z/4 --2--> Z/4):")
    print("  |Ext^n(Z/2, Z/2)|, n = 0..5:", ext_over_zn(4, 2, 2))
    print("  |Ext^n(Z/2, Z/4)|, n = 0..5:", ext_over_zn(4, 2, 4))
    print("Ext over Z/9:")
    print("  |Ext^n(Z/3, Z/3)|, n = 0..5:", ext_over_zn(9, 3, 3))
    print()
    print("Extensions 0 -> Z/p -> E -> Z/p -> 0, counted as cocycles:")
    for p in (2, 3):
        total, cyclic = extension_classes(p)
        print(f"  p = {p}: {total} classes = |Ext^1(Z/{p}, Z/{p})|; "
              f"{cyclic} with E = Z/{p * p}, {total - cyclic} split")
    print()
    print("Epistemic status: exact counts, exhaustive over the finite groups")
    print("shown. They illustrate (not prove) Ext^n(M, N) = Hom_D(M, N[n]),")
    print("Z having global dimension 1 while Z/4 and Z/9 have infinite global")
    print("dimension, and Ext^1 as classes of extensions. That Ext does not")
    print("depend on the resolution chosen is a theorem, not checked here.")


if __name__ == "__main__":
    main()
