"""Pentagons, associahedra and a twisted associator.

Bracketings of n objects are the vertices of the associahedron; one
application of an associator (X Y) Z -> X (Y Z) inside a bracketing is an
edge. For n = 4 the graph is the pentagon. Mac Lane's coherence theorem says
that once the pentagon commutes, every diagram of associators commutes.

We test this in the category of Z/n-graded vector spaces with associator
twisted by a function w(a, b, c) in Z/n (the exponent of a root of unity).
The pentagon for simple objects is the 3-cocycle condition. For the carry
cochain w(a, b, c) = p * a * carry(b, c) it holds, and then every path
between two bracketings of five graded objects has the same total twist;
for a naive guess it fails, and so does path-independence. Exact integer
arithmetic; exhaustive over the finite ranges stated.
"""

import itertools

EXPERIMENT = {
    "id": "monoidal_categories_pentagon",
    "title": "Pentagons, associahedra and a twisted associator",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["monoidal-categories"],
    "summary": (
        "Builds the associahedron graphs (bracketings and associator moves) "
        "for up to six objects, checks the 3-cocycle (pentagon) condition for "
        "the carry cochain on Z/n for n up to 6, and verifies that all paths "
        "between bracketings of five graded objects carry the same twist - "
        "while a naive twist fails both tests. Exhaustive, exact, finite."
    ),
    "packages": [],
}


def bracketings(leaves):
    """All full bracketings of a tuple of leaves, as nested pairs."""
    if len(leaves) == 1:
        return [leaves[0]]
    out = []
    for k in range(1, len(leaves)):
        for left in bracketings(leaves[:k]):
            for right in bracketings(leaves[k:]):
                out.append((left, right))
    return out


def moves(tree):
    """All (result, (x, y, z)) for one associator ((x y) z) -> (x (y z))."""
    out = []
    if isinstance(tree, tuple):
        left, right = tree
        if isinstance(left, tuple):
            x, y = left
            out.append(((x, (y, right)), (x, y, right)))
        out += [((new, right), xyz) for new, xyz in moves(left)]
        out += [((left, new), xyz) for new, xyz in moves(right)]
    return out


def associahedron(n):
    """(number of vertices, number of edges) for bracketings of n objects."""
    trees = bracketings(tuple(range(n)))
    edges = sum(len(moves(t)) for t in trees)
    return len(trees), edges


def carry(b, c, n):
    """1 if b + c wraps around modulo n, else 0."""
    return 1 if b + c >= n else 0


def carry_cochain(p, n):
    """The cochain w(a, b, c) = p * a * carry(b, c) mod n."""
    return lambda a, b, c: p * a * carry(b, c, n) % n


def naive_cochain(n):
    """A wrong guess: twist by the carry of the first two indices."""
    return lambda a, b, c: carry(a, b, n)


def cocycle_failures(w, n):
    """Quadruples (a, b, c, d) where the pentagon (cocycle) condition fails."""
    bad = []
    for a, b, c, d in itertools.product(range(n), repeat=4):
        lhs = w(b, c, d) + w(a, (b + c) % n, d) + w(a, b, c)
        rhs = w((a + b) % n, c, d) + w(a, b, (c + d) % n)
        if (lhs - rhs) % n:
            bad.append((a, b, c, d))
    return bad


def path_independent(w, grades, n):
    """True if all associator paths between bracketings carry the same twist.

    The twist of a move ((x y) z) -> (x (y z)) is w(deg x, deg y, deg z);
    going backwards along a move contributes minus that twist. Leaves are
    tagged with their position, and grades[i] is the grade of leaf i. We
    try to assign each bracketing a "potential" consistent with every edge.
    """
    trees = bracketings(tuple(range(len(grades))))

    def deg(t):
        if isinstance(t, tuple):
            return (deg(t[0]) + deg(t[1])) % n
        return grades[t] % n

    neighbours = {t: [] for t in trees}
    for tree in trees:
        for new, (x, y, z) in moves(tree):
            twist = w(deg(x), deg(y), deg(z))
            neighbours[tree].append((new, twist))
            neighbours[new].append((tree, -twist))
    potential = {trees[0]: 0}
    frontier = [trees[0]]
    while frontier:
        tree = frontier.pop()
        for new, twist in neighbours[tree]:
            value = (potential[tree] + twist) % n
            if new not in potential:
                potential[new] = value
                frontier.append(new)
            elif potential[new] != value:
                return False
    return len(potential) == len(trees)


def main():
    print("Associahedra: bracketings (vertices) and associator moves (edges)")
    for n in range(2, 7):
        v, e = associahedron(n)
        print(f"  {n} objects: {v:3d} bracketings, {e:3d} moves")
    print("Pentagon = 3-cocycle condition for w(a,b,c) = p*a*carry(b,c) mod n")
    for n in range(2, 7):
        bad = sum(len(cocycle_failures(carry_cochain(p, n), n))
                  for p in range(n))
        print(f"  Z/{n}: all {n} values of p, {n ** 4} quadruples each: "
              f"{bad} failures")
    naive = cocycle_failures(naive_cochain(3), 3)
    print(f"  naive w(a,b,c) = carry(a,b) on Z/3: {len(naive)} failures, "
          f"first {naive[0]}")
    print("Coherence: all paths in the associahedron for 5 graded objects")
    grades = list(itertools.product(range(3), repeat=5))
    good = sum(path_independent(carry_cochain(1, 3), g, 3) for g in grades)
    bad = sum(path_independent(naive_cochain(3), g, 3) for g in grades)
    print(f"  carry cochain, p = 1: {good} of {len(grades)} gradings "
          "path-independent")
    print(f"  naive cochain:        {bad} of {len(grades)} gradings "
          "path-independent")
    print()
    print("Epistemic status: exact, exhaustive checks over the finite ranges "
          "shown.\nThey illustrate Mac Lane's coherence theorem (pentagon => "
          "all diagrams\ncommute) in one family of examples; the theorem "
          "itself, and the cocycle\nidentity for every n, are proved in the "
          "lesson, not here.")


if __name__ == "__main__":
    main()
