"""Closed sets of Cantor space as trees: what finite information can and cannot see.

Every closed subset of Cantor space 2^N is the set [T] of infinite branches of
a pruned tree T of finite binary strings. The perfect set theorem for closed
sets (Cantor-Bendixson) says [T] is either countable or contains a perfect
set - equivalently, T contains a copy of the full binary tree - and then has
cardinality 2^aleph_0.

We look at four trees, truncated at depth N:
  full       all strings                  [T] = 2^N, perfect
  golden     no two adjacent 1s           perfect, uncountable
  at most 2  at most two 1s               countable (Cantor-Bendixson rank 3)
  staircase  if the first 1 is at place j, countable (every branch has
             at most j further 1s         finitely many 1s)
For each we count the nodes at depth N, compute the splitting height (the
height of the largest full binary tree whose branching nodes are branching
nodes of T), and test whether every node branches somewhere above it.

The staircase tree is the point: its node counts and splitting heights are
exactly those of the golden tree, yet it has only countably many branches.
Finite truncations cannot tell a countable closed set from a perfect one.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from functools import lru_cache
import textwrap

EXPERIMENT = {
    "id": "descriptive_set_theory_trees",
    "title": "Closed sets as trees: perfect versus countable",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["descriptive-set-theory"],
    "summary": (
        "Counts nodes and computes splitting heights of four pruned binary trees "
        "truncated at depths up to 16, and tests whether every node branches. A "
        "perfect tree and a countable 'staircase' tree turn out to have identical "
        "counts and splitting heights: the perfect set dichotomy is a theorem about "
        "infinite trees that finite truncations cannot decide."
    ),
    "packages": [],
}


def full(s):
    """Every binary string."""
    return True


def golden(s):
    """No two adjacent 1s (the golden-mean shift)."""
    return "11" not in s


def at_most_two(s):
    """At most two 1s."""
    return s.count("1") <= 2


def staircase(s):
    """If the first 1 is at position j, at most j further 1s follow it."""
    j = s.find("1")
    return j < 0 or s[j + 1:].count("1") <= j


TREES = [("full", full), ("golden", golden), ("at most 2", at_most_two),
         ("staircase", staircase)]


def level(tree, n):
    """The nodes of the tree at depth n (strings of length n)."""
    nodes = [""]
    for _ in range(n):
        nodes = [t + b for t in nodes for b in "01" if tree(t + b)]
    return nodes


def splitting_height(tree, n, node=""):
    """Height of the largest full binary tree embedded in the tree's branching
    nodes above ``node``, within depth n."""

    @lru_cache(maxsize=None)
    def height(t):
        if len(t) == n:
            return 0
        kids = [t + b for b in "01" if tree(t + b)]
        best = max(height(c) for c in kids)
        if len(kids) == 2:
            best = max(best, 1 + min(height(kids[0]), height(kids[1])))
        return best

    if not tree(node):
        raise ValueError("node is not in the tree")
    return height(node)


def every_node_branches(tree, n):
    """Does every node of depth <= n - 2 have a branching node above it within
    depth n? (A finite test of perfectness.)"""
    for depth in range(n - 1):
        for t in level(tree, depth):
            if splitting_height(tree, n, t) == 0:
                return False
    return True


def main():
    depths = (4, 8, 12, 16)
    print("Pruned trees T on {0,1}, truncated at depth N")
    print("              nodes at depth N           splitting height    every node")
    print("tree        " + "".join(f"{f'N={d}':>7}" for d in depths)
          + "     " + "".join(f"{d:>4}" for d in depths) + "    branches")
    for name, tree in TREES:
        counts = "".join(f"{len(level(tree, d)):>7}" for d in depths)
        heights = "".join(f"{splitting_height(tree, d):>4}" for d in depths)
        print(f"{name:<12}{counts}     {heights}    {every_node_branches(tree, 10)}")
    same = all(len(level(golden, d)) == len(level(staircase, d)) and
               splitting_height(golden, d) == splitting_height(staircase, d)
               for d in range(1, 17))
    print()
    print(f"golden and staircase agree on both statistics for N = 1..16: {same}")
    print("but [golden] is perfect (uncountable) while [staircase] is countable.")
    print()
    print(textwrap.fill(
        "Epistemic status: exact counts for finite truncations. The finite branch "
        "test detects that the 'at most 2' and staircase trees are not perfect, "
        "but neither statistic can decide whether a tree has uncountably many "
        "branches: that is a theorem about the infinite tree (here, every "
        "staircase branch has finitely many 1s). Hurewicz showed that the codes "
        "of countable closed sets form a coanalytic, non-Borel set.",
        width=78,
    ))


if __name__ == "__main__":
    main()
