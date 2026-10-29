"""A relation checker: properties, counterexamples and classes.

Give it a finite set and a yes/no rule for pairs. It tests reflexivity,
symmetry and transitivity by running through every case, prints a
counterexample for each property that fails, and, when the rule is an
equivalence relation, prints its classes - which always come out as a
partition. On a finite set this exhaustive check is a proof for that set;
it says nothing about larger sets.
"""

EXPERIMENT = {
    "id": "equivalence_relations_checker",
    "title": "A relation checker: counterexamples and classes",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["equivalence-relations"],
    "summary": (
        "Tests six relations on small finite sets - same remainder, differ "
        "by at most 1, divides, less than, same number of letters and share "
        "a letter - for reflexivity, symmetry and transitivity by checking "
        "every case. Prints a counterexample for each failure and the "
        "equivalence classes of each equivalence relation, checking that "
        "they form a partition. Valid for these finite sets only."
    ),
    "packages": [],
}


def reflexive_counterexample(elements, rel):
    """An a with not rel(a, a), or None if rel is reflexive."""
    for a in elements:
        if not rel(a, a):
            return (a,)
    return None


def symmetric_counterexample(elements, rel):
    """A pair (a, b) with rel(a, b) but not rel(b, a), or None."""
    for a in elements:
        for b in elements:
            if rel(a, b) and not rel(b, a):
                return (a, b)
    return None


def transitive_counterexample(elements, rel):
    """A triple (a, b, c) with rel(a, b), rel(b, c), not rel(a, c), or None."""
    for a in elements:
        for b in elements:
            if not rel(a, b):
                continue
            for c in elements:
                if rel(b, c) and not rel(a, c):
                    return (a, b, c)
    return None


def equivalence_classes(elements, rel):
    """The classes [a] = [x for x in elements if rel(x, a)], without repeats,
    in order of first appearance."""
    found = []
    for a in elements:
        cls = [x for x in elements if rel(x, a)]
        if cls not in found:
            found.append(cls)
    return found


def is_partition(elements, blocks):
    """Blocks are non-empty, pairwise disjoint and together cover elements."""
    members = [x for block in blocks for x in block]
    return (all(blocks) and len(members) == len(set(members))
            and set(members) == set(elements))


def same_letters_count(u, v):
    return len(u) == len(v)


def share_a_letter(u, v):
    return bool(set(u.lower()) & set(v.lower()))


COUNTRIES = ["Chad", "Peru", "Iran", "Fiji", "Ghana", "Nepal", "Kenya",
             "Malta", "Japan", "Bhutan", "Mexico", "Canada"]

RELATIONS = [
    ("same remainder mod 3", list(range(12)), lambda a, b: a % 3 == b % 3),
    ("differ by at most 1", list(range(6)), lambda a, b: abs(a - b) <= 1),
    ("a divides b", list(range(1, 7)), lambda a, b: b % a == 0),
    ("a is less than b", list(range(6)), lambda a, b: a < b),
    ("same number of letters", COUNTRIES, same_letters_count),
    ("share a letter", COUNTRIES, share_a_letter),
]


def report(name, elements, rel):
    """Lines of text describing one relation."""
    checks = [("reflexive", reflexive_counterexample(elements, rel)),
              ("symmetric", symmetric_counterexample(elements, rel)),
              ("transitive", transitive_counterexample(elements, rel))]
    verdict = ", ".join(("" if cx is None else "not ") + p for p, cx in checks)
    lines = [f"{name}: {verdict}"]
    for prop, cx in checks:
        if cx is not None:
            shown = ", ".join(str(x) for x in cx)
            lines.append(f"   fails {prop}: ({shown})")
    if all(cx is None for _, cx in checks):
        blocks = equivalence_classes(elements, rel)
        shown = ["{" + ",".join(str(x) for x in b) + "}" for b in blocks]
        line = f"   {len(blocks)} classes: {' '.join(shown)}"
        if len(line) <= 80:
            lines.append(line)
        else:  # one class per line, to keep within 80 characters
            lines.append(f"   {len(blocks)} classes:")
            lines.extend(f"     {b}" for b in shown)
        lines.append(f"   the classes form a partition: {is_partition(elements, blocks)}")
    return lines


def main():
    for name, elements, rel in RELATIONS:
        for line in report(name, elements, rel):
            print(line)
    print()
    print("Epistemic status: every case on these finite sets was checked, so")
    print("each verdict is proved for that set - and one counterexample")
    print("settles a failure for good. A rule that passes on a small set may")
    print("still fail on a larger one; for 'same remainder' on all of Z the")
    print("lesson gives a proof.")


if __name__ == "__main__":
    main()
