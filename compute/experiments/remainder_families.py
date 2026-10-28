"""Remainder families: splitting the integers into residue classes.

Two integers belong to the same *family* (residue class) mod k when they leave
the same remainder on division by k. We split -12..12 into families, check
that the families never overlap and together contain every number, and check
that the family of a sum (or product) depends only on the families of the
numbers being added - so "family + family" makes sense. Finally we show an
operation that does NOT respect families.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
import textwrap

EXPERIMENT = {
    "id": "remainder_families",
    "title": "Remainder families: residue classes that add up",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["remainder-families"],
    "summary": (
        "Splits the integers -12..12 into residue classes mod k, checks for k = 1 "
        "to 12 that the classes are disjoint and cover the range, and that the "
        "class of a sum or product depends only on the classes of the inputs, for "
        "every choice of representatives in that range. This is evidence for the "
        "general theorem, not a proof of it; a counterexample shows powers do not "
        "respect classes in the exponent."
    ),
    "packages": [],
}

NUMBERS = range(-12, 13)


def residue(n, k):
    """The remainder of n on division by k, always in 0..k-1 (Python's % does this even for n < 0)."""
    if k < 1:
        raise ValueError("the modulus k must be at least 1")
    return n % k


def residue_classes(numbers, k):
    """Split ``numbers`` into families mod k: {remainder: [numbers with that remainder]}.

    Every remainder 0..k-1 appears as a key, even if its family is empty.
    """
    classes = {r: [] for r in range(k)}
    for n in numbers:
        classes[residue(n, k)].append(n)
    return classes


def is_partition(classes, numbers):
    """True when the families are pairwise disjoint and together contain exactly ``numbers``."""
    seen = []
    for members in classes.values():
        seen.extend(members)
    return len(seen) == len(set(seen)) and set(seen) == set(numbers)


def depends_only_on_classes(op, numbers, k, second=None):
    """Check that residue(op(a, b)) depends only on residue(a) and residue(b).

    ``a`` runs over ``numbers`` and ``b`` over ``second`` (default: ``numbers``).
    Returns ``(cases, counterexample)`` where counterexample is None, or a pair
    of input pairs ((a, b), (a2, b2)) in the same classes whose results land in
    different classes.
    """
    second = numbers if second is None else second
    first_seen = {}
    cases = 0
    for a, b in product(numbers, second):
        cases += 1
        key = (residue(a, k), residue(b, k))
        result = residue(op(a, b), k)
        if key not in first_seen:
            first_seen[key] = ((a, b), result)
        elif first_seen[key][1] != result:
            return cases, (first_seen[key][0], (a, b))
    return cases, None


def class_table(op, k):
    """The table of op on classes mod k, computed from the representatives 0..k-1."""
    return [[residue(op(a, b), k) for b in range(k)] for a in range(k)]


def add(a, b):
    """a + b"""
    return a + b


def mul(a, b):
    """a * b"""
    return a * b


def power(a, b):
    """a ** b (used with non-negative exponents b only)"""
    return a ** b


def main():
    k = 3
    print(f"Families mod {k} for the integers -12..12 (Python's % gives remainders 0..{k - 1}):")
    for r, members in residue_classes(NUMBERS, k).items():
        print(f"  [{r}]: " + " ".join(f"{n:>3}" for n in members))
    print(f"  For example -7 = 3 * (-3) + 2, so -7 is in family [2].")
    print()
    moduli = range(1, 13)
    partitions = all(is_partition(residue_classes(NUMBERS, m), NUMBERS) for m in moduli)
    print(f"k = 1..12: families are disjoint and cover -12..12 for every k: {partitions}")
    for name, op in [("a + b", add), ("a * b", mul)]:
        total, broken = 0, []
        for m in moduli:
            cases, bad = depends_only_on_classes(op, NUMBERS, m)
            total += cases
            if bad:
                broken.append(m)
        print(f"  family of {name} depends only on the families of a and b: "
              f"{'yes' if not broken else 'NO for k = ' + str(broken)} ({total} cases)")
    print()
    print(f"So families can be added. The addition table of families mod {k}:")
    print("   + | " + "  ".join(f"[{b}]" for b in range(k)))
    for a, row in enumerate(class_table(add, k)):
        print(f"  [{a}]| " + "  ".join(f"[{v}]" for v in row))
    print()
    _, bad = depends_only_on_classes(power, [2], k, second=range(0, 7))
    (a1, b1), (a2, b2) = bad
    print(f"Not every operation respects families. Try powers of 2 mod {k}, exponents 0..6:")
    print(f"  exponents {b1} and {b2} are both in family [{residue(b1, k)}], but")
    print(f"  {a1}^{b1} = {a1 ** b1} is in [{residue(a1 ** b1, k)}] while "
          f"{a2}^{b2} = {a2 ** b2} is in [{residue(a2 ** b2, k)}].")
    print()
    print(textwrap.fill(
        "Epistemic status: every pair of numbers in -12..12 was checked for each k "
        "from 1 to 12. That is strong evidence, but it is not a proof that family "
        "addition works for all integers; the lesson's argument (if a - a2 and "
        "b - b2 are multiples of k, so is (a + b) - (a2 + b2)) is. The power "
        "example is a genuine counterexample.",
        width=78,
    ))


if __name__ == "__main__":
    main()
