"""How many ways can a small set be ordered? An exhaustive census of posets.

Every partial order on an n-element set is a reflexive relation, so it is
enough to try all 2^(n(n-1)) choices of the off-diagonal pairs. For n <= 4 the
experiment counts the preorders, the partial orders, the total orders and the
lattices among them, and checks on every partial order the lesson's theorem
that a finite non-empty poset has a maximal element - and that "maximal"
and "greatest" really differ. The counts are exact and exhaustive for these
sizes (they agree with the published values: 1, 3, 19, 219 partial orders);
they prove nothing for larger n.
"""

import itertools
import math

EXPERIMENT = {
    "id": "order_theory_counting_posets",
    "title": "A census of all partial orders on small sets",
    "evidence": ["exhaustive-finite", "exact"],
    "lessons": ["order-theory"],
    "summary": (
        "Tries every reflexive relation on sets of 1 to 4 elements, counting "
        "preorders, partial orders (1, 3, 19, 219), total orders (n!) and lattices, "
        "and checks on each partial order that a maximal element exists, and how "
        "often there is a greatest one. Exhaustive and exact for n <= 4 only."
    ),
    "packages": [],
}


def reflexive_relations(n):
    """Yield every reflexive relation on range(n) as a set of pairs."""
    off = [(a, b) for a in range(n) for b in range(n) if a != b]
    diag = {(a, a) for a in range(n)}
    for bits in itertools.product((0, 1), repeat=len(off)):
        yield diag | {p for p, bit in zip(off, bits) if bit}


def is_transitive(rel, n):
    """(a, b) and (b, c) in rel imply (a, c) in rel."""
    return all((a, c) in rel for (a, b) in rel for c in range(n)
               if (b, c) in rel)


def is_antisymmetric(rel):
    """(a, b) and (b, a) in rel imply a = b."""
    return all(a == b or (b, a) not in rel for (a, b) in rel)


def is_total(rel, n):
    """Any two elements are comparable."""
    return all((a, b) in rel or (b, a) in rel
               for a in range(n) for b in range(n))


def maximal_elements(rel, n):
    """Elements with nothing strictly above them."""
    return [m for m in range(n)
            if not any((m, x) in rel and x != m for x in range(n))]


def greatest_element(rel, n):
    """The element above everything, or None."""
    tops = [g for g in range(n) if all((x, g) in rel for x in range(n))]
    return tops[0] if tops else None


def join(rel, n, a, b):
    """The least upper bound of a and b, or None if it does not exist."""
    ups = [u for u in range(n) if (a, u) in rel and (b, u) in rel]
    least = [u for u in ups if all((u, v) in rel for v in ups)]
    return least[0] if least else None


def meet(rel, n, a, b):
    """The greatest lower bound of a and b, or None."""
    return join({(y, x) for (x, y) in rel}, n, a, b)


def is_lattice(rel, n):
    """Every pair has a join and a meet."""
    return all(join(rel, n, a, b) is not None and meet(rel, n, a, b)
               is not None for a in range(n) for b in range(n))


def census(n):
    """Counts for all relations on an n-element set."""
    c = {"preorders": 0, "partial orders": 0, "total orders": 0,
         "lattices": 0, "with greatest": 0, "max ok": True}
    for rel in reflexive_relations(n):
        if not is_transitive(rel, n):
            continue
        c["preorders"] += 1
        if not is_antisymmetric(rel):
            continue
        c["partial orders"] += 1
        c["total orders"] += is_total(rel, n)
        c["lattices"] += is_lattice(rel, n)
        c["with greatest"] += greatest_element(rel, n) is not None
        c["max ok"] = c["max ok"] and bool(maximal_elements(rel, n))
    return c


def main():
    print(" n  preorders  partial  total  n!  lattices  with greatest")
    every = True
    for n in range(1, 5):
        c = census(n)
        every = every and c["max ok"]
        print(f"{n:>2}  {c['preorders']:>9}  {c['partial orders']:>7}"
              f"  {c['total orders']:>5}  {math.factorial(n):>2}"
              f"  {c['lattices']:>8}  {c['with greatest']:>13}")
    print("every partial order (n <= 4) has a maximal element:", every)
    v = {(0, 0), (1, 1), (2, 2), (0, 1), (0, 2)}
    print("the 'V' shape 0 < 1, 0 < 2: maximal", maximal_elements(v, 3),
          "greatest", greatest_element(v, 3), "join(1, 2)", join(v, 3, 1, 2))
    print()
    print("Epistemic status: an exact, exhaustive count for sets of at most")
    print("four elements, agreeing with the known values. It illustrates that")
    print("most partial orders are neither total nor lattices, and confirms")
    print("the maximal-element theorem for these cases only; the lesson proves")
    print("it for every finite poset.")


if __name__ == "__main__":
    main()
