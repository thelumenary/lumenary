"""Telling groups apart with hom functors, and where that fails.

A functor sends isomorphic objects to isomorphic objects. For the hom
functor Hom(Z/n, -) from groups to sets this means: if G and H are
isomorphic, then |Hom(Z/n, G)| = |Hom(Z/n, H)|. A homomorphism Z/n -> G is
determined by the image g of 1, which can be any g with g^n = e, so the
count is #{g in G : g^n = e}. We compute these counts for the five groups of
order 8, which they tell apart completely, and for Z/4 x Z/4 and Z/2 x Q8 of
order 16, which they cannot tell apart. A different hom functor,
Hom(Z x Z, -) (commuting pairs), separates that last pair. Exact computation
on finite groups.
"""

from itertools import product

EXPERIMENT = {
    "id": "functors_hom_counts",
    "title": "Telling groups apart with hom functors",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["functors"],
    "summary": (
        "Counts homomorphisms Z/n -> G (elements with g^n = e) for the five "
        "groups of order 8 and for Z/4 x Z/4 and Z/2 x Q8, and counts "
        "homomorphisms Z x Z -> G (commuting pairs). Equal counts never prove "
        "two groups isomorphic; different counts prove they are not, because "
        "functors preserve isomorphisms. Exact computation on finite groups."
    ),
    "packages": [],
}


def cyclic(n):
    """The cyclic group Z/n: (elements, multiplication, identity)."""
    return list(range(n)), (lambda a, b: (a + b) % n), 0


def direct_product(g, h):
    """The direct product of two groups, with coordinatewise operation."""
    (ge, gm, g1), (he, hm, h1) = g, h
    elements = list(product(ge, he))
    return elements, (lambda a, b: (gm(a[0], b[0]), hm(a[1], b[1]))), (g1, h1)


def dihedral8():
    """Symmetries of a square: (r, s) means rotate by r quarter turns, then
    reflect if s = 1."""
    def mul(a, b):
        r1, s1 = a
        r2, s2 = b
        return ((r1 + (r2 if s1 == 0 else -r2)) % 4, (s1 + s2) % 2)
    return list(product(range(4), range(2))), mul, (0, 0)


def quaternion8():
    """Q8 = {+-1, +-i, +-j, +-k} as unit quaternions (a, b, c, d)."""
    def mul(p, q):
        a1, b1, c1, d1 = p
        a2, b2, c2, d2 = q
        return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
                a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
                a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
                a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)
    units = []
    for k in range(4):
        for sign in (1, -1):
            units.append(tuple(sign if i == k else 0 for i in range(4)))
    return units, mul, (1, 0, 0, 0)


def power(group, g, n):
    """g^n in the group, by repeated multiplication."""
    _, mul, one = group
    result = one
    for _ in range(n):
        result = mul(result, g)
    return result


def hom_count_cyclic(group, n):
    """|Hom(Z/n, G)| = number of g with g^n = e."""
    elements, _, one = group
    return sum(1 for g in elements if power(group, g, n) == one)


def commuting_pairs(group):
    """|Hom(Z x Z, G)| = number of pairs (a, b) with ab = ba."""
    elements, mul, _ = group
    return sum(1 for a in elements for b in elements if mul(a, b) == mul(b, a))


def groups_of_order_8():
    """The five groups of order 8, up to isomorphism, with names."""
    z2, z4 = cyclic(2), cyclic(4)
    return [
        ("Z/8", cyclic(8)),
        ("Z/4 x Z/2", direct_product(z4, z2)),
        ("Z/2 x Z/2 x Z/2", direct_product(direct_product(z2, z2), z2)),
        ("D4 (square)", dihedral8()),
        ("Q8", quaternion8()),
    ]


def main():
    print("|Hom(Z/n, G)| = #{g : g^n = e}")
    print(f"{'G':<18}{'n=1':>5}{'n=2':>5}{'n=4':>5}{'n=8':>5}")
    signatures = []
    for name, group in groups_of_order_8():
        row = [hom_count_cyclic(group, n) for n in (1, 2, 4, 8)]
        signatures.append(tuple(row))
        print(f"{name:<18}" + "".join(f"{c:>5}" for c in row))
    distinct = len(set(signatures)) == len(signatures)
    print(f"All five rows differ, so no two are isomorphic: {distinct}")
    print()
    z2, z4 = cyclic(2), cyclic(4)
    pair = [("Z/4 x Z/4", direct_product(z4, z4)),
            ("Z/2 x Q8", direct_product(z2, quaternion8()))]
    print("Order 16:")
    for name, group in pair:
        row = [hom_count_cyclic(group, n) for n in (1, 2, 4, 8, 16)]
        print(f"  {name:<10} |Hom(Z/n, G)|, n = 1, 2, 4, 8, 16: {row}")
    for name, group in pair:
        print(f"  {name:<10} |Hom(Z x Z, G)| = {commuting_pairs(group)}")
    print("Hom(Z/n, -) cannot separate them; Hom(Z x Z, -) can.")
    print()
    print("Epistemic status: exact counts for these finite groups. Different")
    print("counts prove non-isomorphism, because functors preserve")
    print("isomorphisms. Equal counts prove nothing: Z/4 x Z/4 is abelian and")
    print("Z/2 x Q8 is not, yet every Hom(Z/n, -) gives the same numbers.")


if __name__ == "__main__":
    main()
