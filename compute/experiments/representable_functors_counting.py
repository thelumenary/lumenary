"""Representable functors in finite examples: checking and counting.

Three exact, exhaustive checks on small finite sets and groups.
(1) Subsets are characteristic functions: for all sets X, Y with at most 3
elements and all maps f : Y -> X, the characteristic function of f^-1(S) is
chi_S composed with f (naturality of P(X) = Hom(X, 2)).
(2) Homomorphisms out of a presented group are solutions of its relations: we
count all homomorphisms Z/n -> S3 and V4 -> S3 by brute force over every
function and compare with the number of elements g with g^n = 1, and of
commuting pairs of involutions.
(3) A counting test: a representable functor on finite sets has |F(n)| = n^a
(covariant) or a^n (contravariant). Sequences that fit no such formula
belong to functors that cannot be representable.
"""

import itertools

EXPERIMENT = {
    "id": "representable_functors_counting",
    "title": "Representable functors on finite sets and groups, by brute force",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["representable-functors"],
    "summary": (
        "Checks naturality of subsets versus characteristic functions for all "
        "maps between sets of size <= 3; counts all homomorphisms Z/n -> S3 "
        "and V4 -> S3 by brute force and matches them with solutions of the "
        "defining relations (the representing property of presentations); and "
        "applies the counting test |F(n)| = n^a or a^n to show that several "
        "functors on finite sets are not representable. Exhaustive in these "
        "finite cases only."
    ),
    "packages": [],
}


def maps(dom, cod):
    """All functions dom -> cod, as tuples indexed by dom = range(len)."""
    return list(itertools.product(range(cod), repeat=dom))


def subsets(n):
    """All subsets of range(n), as frozensets."""
    return [frozenset(c) for k in range(n + 1)
            for c in itertools.combinations(range(n), k)]


def chi(s, n):
    """The characteristic function of s ⊆ range(n), as a tuple of 0/1."""
    return tuple(1 if x in s else 0 for x in range(n))


def preimage(f, s):
    """f^-1(s) for f given as a tuple."""
    return frozenset(y for y, fy in enumerate(f) if fy in s)


def powerset_naturality(max_size=3):
    """Check chi(f^-1(S)) = chi(S) ∘ f for all f : Y -> X, S ⊆ X; return the
    number of checks and the number of failures."""
    checks = failures = 0
    for n in range(max_size + 1):
        for m in range(max_size + 1):
            for f in maps(m, n):
                for s in subsets(n):
                    checks += 1
                    lhs = chi(preimage(f, s), m)
                    rhs = tuple(chi(s, n)[f[y]] for y in range(m))
                    failures += lhs != rhs
    return checks, failures


# Groups as (elements, multiplication function, identity).

def symmetric_group_3():
    """S3 as permutations of (0, 1, 2); (p*q)(i) = p(q(i))."""
    elems = list(itertools.permutations(range(3)))
    return elems, (lambda p, q: tuple(p[q[i]] for i in range(3))), (0, 1, 2)


def cyclic_group(n):
    """Z/n under addition."""
    return list(range(n)), (lambda a, b: (a + b) % n), 0


def klein_four():
    """V4 = Z/2 x Z/2."""
    elems = [(a, b) for a in range(2) for b in range(2)]
    return elems, (lambda x, y: ((x[0] + y[0]) % 2, (x[1] + y[1]) % 2)), (0, 0)


def count_homs(source, target):
    """Brute force: how many of the functions source -> target respect
    multiplication? (Such functions automatically preserve 1 and inverses.)"""
    s_el, s_mul, _ = source
    t_el, t_mul, _ = target
    count = 0
    for images in itertools.product(t_el, repeat=len(s_el)):
        h = dict(zip(s_el, images))
        if all(h[s_mul(a, b)] == t_mul(h[a], h[b]) for a in s_el for b in s_el):
            count += 1
    return count


def power(g, n, mul, one):
    """g^n in a group."""
    result = one
    for _ in range(n):
        result = mul(result, g)
    return result


def nth_roots_of_one(n, group):
    """Number of g with g^n = 1: the size of Hom(Z/n, G) by representability."""
    elems, mul, one = group
    return sum(power(g, n, mul, one) == one for g in elems)


def commuting_involution_pairs(group):
    """Pairs (x, y) with x^2 = y^2 = 1 and xy = yx: Hom(V4, G)."""
    elems, mul, one = group
    return sum(mul(x, x) == one and mul(y, y) == one and mul(x, y) == mul(y, x)
               for x in elems for y in elems)


def fits_covariant(seq):
    """Return a with seq[n] == n**a for all n (0**0 = 1), or None."""
    for a in range(len(seq) + 3):
        if all(s == n ** a for n, s in enumerate(seq)):
            return a
    return None


def fits_contravariant(seq):
    """Return a with seq[n] == a**n for all n, or None."""
    if len(seq) < 2:
        return None
    a = seq[1]
    return a if all(s == a ** n for n, s in enumerate(seq)) else None


def bell(n):
    """Number of equivalence relations on an n-element set."""
    row, total = [1], 1
    for _ in range(n):
        new = [row[-1]]
        for x in row:
            new.append(new[-1] + x)
        row, total = new, new[0]
    return total if n else 1


def main():
    checks, failures = powerset_naturality(3)
    print("1. Subsets versus maps to {0, 1}: chi(f^-1 S) = chi(S) ∘ f")
    print(f"   all f : Y -> X, S ⊆ X with |X|, |Y| <= 3: {checks} checks,"
          f" {failures} failures")
    print()
    s3 = symmetric_group_3()
    print("2. Homomorphisms into S3: brute force versus the relations")
    for n in range(1, 5):
        print(f"   |Hom(Z/{n}, S3)| = {count_homs(cyclic_group(n), s3):<3}"
              f"  #{{g in S3 : g^{n} = 1}} = {nth_roots_of_one(n, s3)}")
    print(f"   |Hom(V4, S3)|  = {count_homs(klein_four(), s3):<3}"
          f"  #{{(x, y) : x^2 = y^2 = 1, xy = yx}} = "
          f"{commuting_involution_pairs(s3)}")
    print()
    print("3. Counting test on sets of size n = 0..5 (representable => fits)")
    rows = [
        ("contravariant  X -> P(X), preimage", [2 ** n for n in range(6)], "contra"),
        ("contravariant  X -> equivalence relations",
         [bell(n) for n in range(6)], "contra"),
        ("covariant      X -> X × X", [n * n for n in range(6)], "co"),
        ("covariant      X -> P(X), direct image", [2 ** n for n in range(6)], "co"),
        ("covariant      X -> X ⊔ X", [2 * n for n in range(6)], "co"),
    ]
    for label, seq, kind in rows:
        a = fits_contravariant(seq) if kind == "contra" else fits_covariant(seq)
        verdict = f"fits with |A| = {a}" if a is not None else "fits no |A|"
        print(f"   {label:<42} {verdict}")
        print(f"      sizes {seq}")
    print()
    print("Epistemic status: exhaustive, exact checks in these finite cases. "
          "Part 2\nconfirms Hom(Z/n, G) = {g : g^n = 1} for G = S3 only. In "
          "part 3 a\nsequence that fits proves nothing by itself (naturality "
          "is also needed),\nbut one that fits no formula proves that the "
          "functor is not representable.")


if __name__ == "__main__":
    main()
