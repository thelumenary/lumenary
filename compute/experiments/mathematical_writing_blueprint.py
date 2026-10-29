"""A blueprint checker: order, circularity and the status of every claim.

A mathematical paper is a network of definitions and results, each used by
later ones. Formalisation projects record this as a "blueprint": a
dependency graph in which every node carries a status - proved here, cited
from the literature, or conjectured. This program checks a small blueprint:

* does the order of presentation ever use an item before it is stated?
* is there a valid order at all, or is the reasoning circular?
* which results are unconditional, and which silently depend on a
  conjecture (and so are only conditional theorems)?

The example is the skeleton of a short expository note; one result
in it rests on a conjecture, and a second version contains a circularity.
The analysis is exact for the data given; it cannot judge whether the
individual proofs are correct.
"""

import textwrap

EXPERIMENT = {
    "id": "mathematical_writing_blueprint",
    "title": "Blueprint check: forward references, circularity, conditional results",
    "evidence": ["exact"],
    "lessons": ["mathematical-writing"],
    "summary": (
        "Takes the dependency graph of a short expository note, with each item "
        "marked proved, cited, conjectured or a definition, and computes forward "
        "references in the written order, a valid order by topological sorting, "
        "circular dependencies, and which results are only conditional because they "
        "depend on a conjecture. Exact for the data; it does not check proofs."
    ),
    "packages": [],
}

#: (label, kind, status, uses), in the order the draft presents them.
DRAFT = [
    ("Def 1", "definition", "definition", []),
    ("Thm 3", "theorem", "proved", ["Def 1", "Lem 2"]),
    ("Lem 2", "lemma", "proved", ["Def 1"]),
    ("Thm 4", "theorem", "cited", ["Def 1"]),
    ("Conj 5", "conjecture", "conjectured", ["Def 1"]),
    ("Cor 6", "corollary", "proved", ["Thm 3", "Thm 4"]),
    ("Prop 7", "proposition", "proved", ["Conj 5", "Lem 2"]),
    ("Cor 8", "corollary", "proved", ["Prop 7"]),
]


def forward_references(items):
    """Pairs (item, dependency) where the dependency is stated later."""
    position = {label: i for i, (label, *_rest) in enumerate(items)}
    return [(label, dep) for i, (label, _, _, uses) in enumerate(items)
            for dep in uses if position[dep] > i]


def topological_order(items):
    """A presentation order respecting all dependencies (stable), or None
    if the dependency graph has a cycle."""
    remaining = {label: set(uses) for label, _, _, uses in items}
    order = []
    while remaining:
        ready = [label for label, *_ in items
                 if label in remaining and not remaining[label]]
        if not ready:
            return None
        first = ready[0]
        order.append(first)
        del remaining[first]
        for deps in remaining.values():
            deps.discard(first)
    return order


def find_cycle(items):
    """Some cycle of dependencies, as a list of labels, or None."""
    uses = {label: deps for label, _, _, deps in items}
    state = {}

    def visit(node, path):
        state[node] = "active"
        for dep in uses[node]:
            if state.get(dep) == "active":
                return path[path.index(dep):] + [dep]
            if dep not in state:
                cycle = visit(dep, path + [dep])
                if cycle:
                    return cycle
        state[node] = "done"
        return None

    for label in uses:
        if label not in state:
            cycle = visit(label, [label])
            if cycle:
                return cycle
    return None


def standing(items):
    """For each label: 'unconditional', 'conjecture', or 'conditional on X'.

    A proved result is only as strong as everything it uses."""
    info = {label: (status, uses) for label, _, status, uses in items}
    memo = {}

    def conditions(label):
        if label not in memo:
            status, uses = info[label]
            found = {label} if status == "conjectured" else set()
            for dep in uses:
                found |= conditions(dep)
            memo[label] = found
        return memo[label]

    out = {}
    for label, _, status, _ in items:
        if status == "conjectured":
            out[label] = "conjecture (stated, not proved)"
        else:
            conds = sorted(conditions(label))
            out[label] = ("conditional on " + ", ".join(conds)) if conds \
                else "unconditional"
    return out


def main():
    print("Draft order:", ", ".join(label for label, *_ in DRAFT))
    for item, dep in forward_references(DRAFT):
        print(f"  forward reference: {item} uses {dep}, which is stated later")
    print("A valid order:", ", ".join(topological_order(DRAFT)))
    print()
    print("Status of each item:")
    marks = standing(DRAFT)
    for label, kind, status, _ in DRAFT:
        print(f"  {label:<7} {kind:<12} {status:<12} -> {marks[label]}")
    print()
    circular = DRAFT + [("Lem 9", "lemma", "proved", ["Cor 10"]),
                        ("Cor 10", "corollary", "proved", ["Lem 9", "Thm 3"])]
    print("Second draft with two new items, Lem 9 and Cor 10:")
    print(f"  valid order exists: {topological_order(circular) is not None}")
    print(f"  circular reasoning: {' -> '.join(find_cycle(circular))}")
    print()
    print(textwrap.fill(
        "Epistemic status: an exact analysis of the dependency data as "
        "written. It finds forward references, circularity and hidden "
        "dependence on a conjecture, but it cannot tell whether any "
        "individual proof is correct, or whether the declared dependencies "
        "are complete - that is the reader's (or a proof assistant's) job.",
        width=78,
    ))


if __name__ == "__main__":
    main()
