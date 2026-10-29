"""Counting relations, equivalence relations and partitions on small sets.

A relation on {0, ..., n-1} is any set of ordered pairs, so there are 2^(n*n)
of them. The experiment runs through relations exhaustively, tests the three
properties, and compares the equivalence relations with the partitions of the
set, generated independently. For n <= 4 it confirms that "take the classes"
matches the equivalence relations one-to-one with the partitions, and it
counts the relations that are symmetric and transitive but NOT reflexive.
This is exhaustive-finite evidence; the lesson proves the theorem for every
set.
"""

import itertools

EXPERIMENT = {
    "id": "equivalence_relations_count",
    "title": "Equivalence relations and partitions, counted exhaustively",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["equivalence-relations"],
    "summary": (
        "Runs through every relation on a 3-element set (512) and every "
        "symmetric relation on sets of up to 4 elements, testing reflexivity, "
        "symmetry and transitivity. Checks that taking equivalence classes "
        "matches equivalence relations one-to-one with partitions (counted "
        "by the Bell numbers 1, 2, 5, 15) and counts the symmetric, "
        "transitive relations that fail to be reflexive. Exhaustive for "
        "n <= 4 only; the lesson's proof covers all sets."
    ),
    "packages": [],
}


def is_reflexive(n, rel):
    """Every a in {0..n-1} is related to itself."""
    return all((a, a) in rel for a in range(n))


def is_symmetric(rel):
    """(a, b) in rel always implies (b, a) in rel."""
    return all((b, a) in rel for a, b in rel)


def is_transitive(rel):
    """(a, b) and (b, c) in rel always imply (a, c) in rel."""
    return all((a, d) in rel for a, b in rel for c, d in rel if b == c)


def is_equivalence(n, rel):
    """Reflexive, symmetric and transitive."""
    return is_reflexive(n, rel) and is_symmetric(rel) and is_transitive(rel)


def all_relations(n):
    """Yield every relation on {0..n-1} as a frozenset of pairs (2^(n*n))."""
    pairs = list(itertools.product(range(n), repeat=2))
    for mask in range(2 ** len(pairs)):
        yield frozenset(p for i, p in enumerate(pairs) if mask >> i & 1)


def symmetric_relations(n):
    """Yield every symmetric relation on {0..n-1} (2^(n(n+1)/2) of them)."""
    slots = [(a, b) for a in range(n) for b in range(a, n)]
    for mask in range(2 ** len(slots)):
        rel = set()
        for i, (a, b) in enumerate(slots):
            if mask >> i & 1:
                rel.update({(a, b), (b, a)})
        yield frozenset(rel)


def classes(n, rel):
    """The partition into classes [a] = {x : (x, a) in rel}, as a frozenset."""
    return frozenset(frozenset(x for x in range(n) if (x, a) in rel)
                     for a in range(n))


def set_partitions(n):
    """Yield all partitions of {0..n-1}, built by placing one element at a
    time into an existing block or a new block (no relations involved)."""
    def build(i, blocks):
        if i == n:
            yield frozenset(frozenset(b) for b in blocks)
            return
        for b in blocks:
            b.append(i)
            yield from build(i + 1, blocks)
            b.pop()
        blocks.append([i])
        yield from build(i + 1, blocks)
        blocks.pop()
    yield from build(0, [])


def bell_numbers(count):
    """First `count` Bell numbers B_0, B_1, ... via the Bell triangle."""
    bells, row = [1], [1]
    while len(bells) < count:
        new = [row[-1]]
        for x in row:
            new.append(new[-1] + x)
        row = new
        bells.append(row[0])
    return bells[:count]


def property_counts(n):
    """Counts of reflexive/symmetric/transitive/equivalence relations."""
    counts = {"all": 0, "refl": 0, "symm": 0, "trans": 0, "equiv": 0}
    for rel in all_relations(n):
        r, s, t = is_reflexive(n, rel), is_symmetric(rel), is_transitive(rel)
        counts["all"] += 1
        counts["refl"] += r
        counts["symm"] += s
        counts["trans"] += t
        counts["equiv"] += r and s and t
    return counts


def compare(n):
    """Return (number of equivalence relations, number of partitions,
    whether "take the classes" is a bijection between them, number of
    symmetric and transitive relations) for the set {0..n-1}."""
    equivs, sym_trans = [], 0
    for rel in symmetric_relations(n):
        if is_transitive(rel):
            sym_trans += 1
            if is_reflexive(n, rel):
                equivs.append(rel)
    images = {classes(n, rel) for rel in equivs}
    parts = set(set_partitions(n))
    bijective = images == parts and len(images) == len(equivs)
    return len(equivs), len(parts), bijective, sym_trans


def main():
    c = property_counts(3)
    print("1. Every relation on {0, 1, 2}: 2^9 =", c["all"])
    print(f"   reflexive {c['refl']}, symmetric {c['symm']}, "
          f"transitive {c['trans']}, equivalence {c['equiv']}")
    print()
    print("2. Equivalence relations versus partitions (generated separately)")
    print("   n  equivalences  partitions  Bell  classes match?  symm+trans")
    bells = bell_numbers(6)
    for n in range(1, 5):
        eq, parts, match, st = compare(n)
        print(f"   {n}  {eq:12}  {parts:10}  {bells[n]:4}  "
              f"{'yes' if match else 'NO':>14}  {st:10}")
    print("   Symmetric + transitive relations outnumber the equivalences:")
    print("   the extra ones relate some element to nothing at all. (Their")
    print("   number is the NEXT Bell number: 2, 5, 15, 52.)")
    rel = frozenset({(0, 0)})
    print(f"   An example on {{0, 1}}: {set(rel)} - symmetric "
          f"{is_symmetric(rel)}, transitive {is_transitive(rel)},")
    print(f"   reflexive {is_reflexive(2, rel)} (1 is related to nothing).")
    print()
    print("Epistemic status: exact, exhaustive checks of every case for sets")
    print("with at most 4 elements (at most 3 for the full table). They agree")
    print("with the theorem that equivalence relations and partitions match")
    print("one-to-one, but only the lesson's proof shows it for every set.")


if __name__ == "__main__":
    main()
