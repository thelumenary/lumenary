"""Compactness in miniature: colouring the natural numbers, level by level.

Join two natural numbers when their difference lies in a set D, and colour
the numbers with k colours so that joined numbers get different colours.
Level n of a tree lists the proper colourings of {0, ..., n - 1}; each node's
children extend it by one more number. If some level is empty, a finite piece
of the graph cannot be coloured. If every level is non-empty, Koenig's lemma
(a finitely branching infinite tree has an infinite branch) gives a colouring
of all of N - the compactness theorem in its simplest form. The program builds
the levels, counts dead ends, and follows a branch that survives to the
deepest level computed. Evidence: exact and exhaustive up to the levels
shown; the passage to infinity is the theorem.
"""

EXPERIMENT = {
    "id": "completeness_theorem_konig_colouring",
    "title": "Compactness via Koenig's lemma: colouring N level by level",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["completeness-theorem"],
    "summary": (
        "Builds the tree of proper colourings of {0, ..., n - 1} for 'distance "
        "graphs' on N (numbers joined when their difference is in D). For "
        "D = {1, 3, 4} and 3 colours the tree dies at level 7, a finite "
        "obstruction; for D = {2, 3, 5, 7} and 4 colours it has many dead ends "
        "but survives to level 24, and a surviving branch is the colouring by "
        "n mod 4. Exact up to level 24; Koenig's lemma supplies the infinite part."
    ),
    "packages": [],
}


def levels(depth, k, distances):
    """Lists of proper k-colourings (tuples) of {0..n-1} for n = 0..depth."""
    tree = [[()]]
    for n in range(depth):
        nxt = []
        for c in tree[-1]:
            used = {c[n - d] for d in distances if n - d >= 0}
            nxt.extend(c + (col,) for col in range(k) if col not in used)
        tree.append(nxt)
    return tree


def dead_ends(tree):
    """For each level n < depth, how many nodes have no child at level n + 1."""
    out = []
    for n in range(len(tree) - 1):
        extended = {c[:n] for c in tree[n + 1]}
        out.append(len(tree[n]) - len(extended))
    return out


def surviving_branch(tree):
    """Koenig's choice: the least child that still has descendants at the bottom."""
    bottom = tree[-1]
    if not bottom:
        return None
    branch = ()
    for n in range(len(tree) - 1):
        options = sorted({c[n] for c in bottom if c[:n] == branch})
        branch += (options[0],)
    return branch


def is_proper(colouring, distances):
    """Do numbers at a distance in D always get different colours?"""
    return all(colouring[i] != colouring[i + d]
               for d in distances for i in range(len(colouring) - d))


def main():
    print("Numbers whose difference lies in D must get different colours.")
    print("Level n = proper colourings of {0, ..., n-1}.")
    print()
    tree = levels(10, 3, (1, 3, 4))
    sizes = [len(t) for t in tree]
    print("1. D = {1, 3, 4}, 3 colours. Level sizes:", sizes[:9])
    first_empty = sizes.index(0)
    print(f"   Level {first_empty} is empty: {{0, ..., {first_empty - 1}}} "
          "cannot be 3-coloured, so neither can N.")
    print()
    tree = levels(24, 4, (2, 3, 5, 7))
    sizes = [len(t) for t in tree]
    print("2. D = {2, 3, 5, 7}, 4 colours. Level sizes for n = 0..24:")
    print("  ", sizes[:13])
    print("  ", sizes[13:])
    dead = dead_ends(tree)
    shown = ", ".join(f"{n}: {d}" for n, d in enumerate(dead) if d)
    print("   dead ends by level (nodes with no child):")
    print("  ", shown)
    branch = surviving_branch(tree)
    print("   a branch surviving to level 24, always taking the least colour")
    print("   that still has descendants at level 24:")
    print("  ", "".join(str(c) for c in branch))
    mod4 = tuple(n % 4 for n in range(24))
    print(f"   equals n mod 4: {branch == mod4}; proper: "
          f"{is_proper(branch, (2, 3, 5, 7))}")
    print("   (n mod 4 colours all of N: 2, 3, 5, 7 are not multiples of 4.)")
    print()
    print("Epistemic status: exact, exhaustive enumeration up to level 24. No")
    print("computation reaches infinity: that non-empty levels at every depth")
    print("give a colouring of all of N is Koenig's lemma, a special case of the")
    print("compactness theorem (here a proof by periodicity happens to exist).")


if __name__ == "__main__":
    main()
