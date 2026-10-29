"""Organised lists: outfits, arrangements and handshakes.

A computer is very good at following a system. The program lists outfits
branch by branch, as in a tree diagram, and checks the product rule m x n
for every m and n up to 6. It lists every order of 3 and of 4 children in a
row. Finally it counts handshakes two ways - as ordered pairs (who reaches
out first) and as unordered pairs - to show the double counting.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap
from itertools import combinations, permutations, product

EXPERIMENT = {
    "id": "systematic_listing_trees",
    "title": "Organised lists: outfits, rows of children and handshakes",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["systematic-listing"],
    "summary": (
        "Lists outfits branch by branch like a tree diagram, checks the "
        "product rule m x n for every m, n up to 6, lists every order of 3 "
        "and 4 children (6 and 24), and counts handshakes among n people both "
        "as ordered and unordered pairs. Exact for the sizes shown; the "
        "lesson explains why the patterns continue."
    ),
    "packages": [],
}

SHIRTS = ["red", "blue", "yellow"]
TROUSERS = ["black", "brown"]


def tree_list(first, second):
    """List every (first, second) pair, branch by branch."""
    return [(a, b) for a in first for b in second]


def product_rule_holds(max_size):
    """Check len(tree_list) == m * n for all 1 <= m, n <= max_size."""
    for m in range(1, max_size + 1):
        for n in range(1, max_size + 1):
            listed = tree_list(range(m), range(n))
            if len(listed) != m * n or len(set(listed)) != m * n:
                return False
    return True


def rows(children):
    """Every order of the children in a row, as strings."""
    return ["".join(p) for p in permutations(children)]


def handshakes(n):
    """Each handshake among n people once: pairs (i, j) with i < j."""
    return list(combinations(range(1, n + 1), 2))


def ordered_pairs(n):
    """Pairs (i, j) of different people where order matters."""
    return [(i, j) for i, j in product(range(1, n + 1), repeat=2) if i != j]


def main():
    outfits = tree_list(SHIRTS, TROUSERS)
    print("Tree diagram, branch by branch:")
    for shirt in SHIRTS:
        ends = ", ".join(f"{s}+{t}" for s, t in outfits if s == shirt)
        print(f"  {shirt:<7}-> {ends}")
    print(f"{len(SHIRTS)} shirts x {len(TROUSERS)} trousers"
          f" = {len(outfits)} outfits, all different: "
          f"{len(set(outfits)) == len(outfits)}")
    print(f"Product rule m x n checked for all m, n up to 6:"
          f" {product_rule_holds(6)}")
    print()
    print("Ana, Bo and Chen in a row: " + " ".join(rows("ABC")))
    four = rows("ABCD")
    print(f"Four children: {len(four)} orders, all different:"
          f" {len(set(four)) == len(four)}")
    print()
    print("People  handshakes  ordered pairs  n x (n - 1) / 2")
    for n in range(2, 9):
        print(f"{n:>6}  {len(handshakes(n)):>10}  {len(ordered_pairs(n)):>13}"
              f"  {n * (n - 1) // 2:>15}")
    print("Ordered pairs count every handshake twice: A-B and B-A.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact and exhaustive for the sizes shown - every "
        "list was built and counted. It does not prove the patterns for "
        "bigger numbers; the lesson's tree-diagram argument and the Lean "
        "proofs do that.",
        width=78,
    ))


if __name__ == "__main__":
    main()
