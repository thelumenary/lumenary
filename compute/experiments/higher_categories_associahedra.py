"""Associahedra: the shapes of coherence for associativity, computed exactly.

In a bicategory (or monoidal category) composition is associative only up to
associator 2-cells. The bracketings of a word of n letters are the vertices of
a graph whose edges are single associator moves ((xy)z) <-> (x(yz)); it is the
1-skeleton of Stasheff's associahedron K_n. We enumerate it exhaustively for
small n and check: the number of bracketings is a Catalan number; the graph is
connected (any two bracketings are related by associators); the two directed
paths from the left comb to the right comb for n = 4 have lengths 2 and 3 (the
two sides of Mac Lane's pentagon); and for n = 5 the 2-dimensional faces are 6
pentagons and 3 squares, with V - E + F = 2, and their boundaries span the
cycle space mod 2 (every loop of associators is a sum of faces). This is
exact, exhaustive-finite evidence for these n only; coherence for all n is
Mac Lane's theorem.
"""

from collections import deque
from math import comb

EXPERIMENT = {
    "id": "higher_categories_associahedra",
    "title": "Associahedra: bracketings, associators and the pentagon",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["higher-categories"],
    "summary": (
        "Enumerates all bracketings of n letters (n <= 7) and the graph of single "
        "associator moves, the 1-skeleton of the associahedron K_n. Checks Catalan "
        "counts, connectivity, the pentagon's paths of lengths 2 and 3, and that "
        "K_5 has 6 pentagons and 3 squares with V - E + F = 2. Exhaustive for "
        "these n; Mac Lane's coherence theorem covers every n."
    ),
    "packages": [],
}


def bracketings(letters):
    """All full bracketings of a tuple of letters, as nested pairs."""
    if len(letters) == 1:
        return [letters[0]]
    out = []
    for i in range(1, len(letters)):
        for left in bracketings(letters[:i]):
            for right in bracketings(letters[i:]):
                out.append((left, right))
    return out


def show(t):
    """Write a bracketing as a string, e.g. ((ab)c)d."""
    if isinstance(t, str):
        return t
    a, b = (show(x) if isinstance(x, str) else "(" + show(x) + ")" for x in t)
    return a + b


def moves(t, forward_only=False):
    """Bracketings one associator away from t.

    The forward move is ((x y) z) -> (x (y z)); without ``forward_only`` the
    inverse move (x (y z)) -> ((x y) z) is included too.
    """
    if isinstance(t, str):
        return []
    left, right = t
    out = [(m, right) for m in moves(left, forward_only)]
    out += [(left, m) for m in moves(right, forward_only)]
    if not isinstance(left, str):
        out.append((left[0], (left[1], right)))
    if not forward_only and not isinstance(right, str):
        out.append(((left, right[0]), right[1]))
    return out


def associator_graph(n):
    """Vertices (bracketings of n letters) and undirected edges of K_n."""
    vertices = bracketings(tuple("abcdefgh"[:n]))
    edges = {frozenset((v, w)) for v in vertices for w in moves(v)}
    return vertices, edges


def distances(start, step):
    """Breadth-first distances from ``start`` along the neighbour map ``step``."""
    dist = {start: 0}
    queue = deque([start])
    while queue:
        v = queue.popleft()
        for w in step(v):
            if w not in dist:
                dist[w] = dist[v] + 1
                queue.append(w)
    return dist


def comb_bracketing(n, left=True):
    """The left comb ((ab)c)d... or the right comb a(b(c(d...)))."""
    letters = "abcdefgh"[:n]
    if left:
        t = letters[0]
        for x in letters[1:]:
            t = (t, x)
        return t
    t = letters[-1]
    for x in reversed(letters[:-1]):
        t = (x, t)
    return t


def directed_path_lengths(n):
    """Lengths of all directed paths left comb -> right comb (forward moves)."""
    memo = {}

    def lengths(t):
        if t not in memo:
            nxt = moves(t, forward_only=True)
            memo[t] = {0} if not nxt else {1 + k for s in nxt for k in lengths(s)}
        return memo[t]

    return sorted(lengths(comb_bracketing(n, left=True)))


def contains_block(t, block):
    """Does bracketing t contain a bracket around exactly the letters ``block``?"""
    if isinstance(t, str):
        return False
    if leaves(t) == block:
        return True
    return contains_block(t[0], block) or contains_block(t[1], block)


def leaves(t):
    """The letters of a bracketing, in order, as a string."""
    return t if isinstance(t, str) else leaves(t[0]) + leaves(t[1])


def facets(n):
    """Facets of K_n: for each proper block of >= 2 consecutive letters, the
    set of bracketings that bracket that block (a list of vertex sets)."""
    word = "abcdefgh"[:n]
    vertices = bracketings(tuple(word))
    out = []
    for r in range(2, n):
        for i in range(n - r + 1):
            block = word[i:i + r]
            out.append({v for v in vertices if contains_block(v, block)})
    return out


def gf2_rank(vectors):
    """Rank over GF(2) of vectors given as Python integers (bit masks)."""
    basis = {}
    for v in vectors:
        while v:
            top = v.bit_length() - 1
            if top not in basis:
                basis[top] = v
                break
            v ^= basis[top]
    return len(basis)


def face_boundary_rank(n):
    """GF(2) rank of the boundaries of the 2-faces of K_n, for n = 5.

    Each face is given by its vertex set; its boundary is the set of edges of
    K_n with both ends in the face, encoded as a bit mask over the edges.
    """
    vertices, edges = associator_graph(n)
    index = {e: i for i, e in enumerate(sorted(edges, key=sorted_key))}
    masks = []
    for face in facets(n):
        mask = 0
        for e in edges:
            if e <= face:
                mask |= 1 << index[e]
        masks.append(mask)
    return gf2_rank(masks)


def sorted_key(edge):
    """A deterministic sort key for an undirected edge."""
    return sorted(show(v) for v in edge)


def main():
    print(" n  bracketings  Catalan  edges  connected  diameter  cycle rank")
    for n in range(3, 8):
        vertices, edges = associator_graph(n)
        nbrs = {v: set(moves(v)) for v in vertices}
        reach = distances(vertices[0], nbrs.__getitem__)
        diameter = max(max(distances(v, nbrs.__getitem__).values())
                       for v in vertices)
        catalan = comb(2 * (n - 1), n - 1) // n
        rank = len(edges) - len(vertices) + 1
        print(f"{n:>2} {len(vertices):>12} {catalan:>8} {len(edges):>6} "
              f"{str(len(reach) == len(vertices)):>10} {diameter:>9} "
              f"{rank:>11}")
    print()
    print("Directed paths ((ab)c)d -> a(b(cd)) have lengths",
          directed_path_lengths(4))
    print("  (the two sides of Mac Lane's pentagon).")
    print("n = 5: directed path lengths left comb -> right comb:",
          directed_path_lengths(5))
    sizes = [len(face) for face in facets(5)]
    v5, e5 = associator_graph(5)
    print(f"K_5 faces: {sizes.count(5)} pentagons, {sizes.count(4)} squares; "
          f"V - E + F = {len(v5)} - {len(e5)} + {len(sizes)} = "
          f"{len(v5) - len(e5) + len(sizes)}")
    print(f"GF(2) rank of the face boundaries: {face_boundary_rank(5)} = cycle "
          f"rank {len(e5) - len(v5) + 1}: mod 2,")
    print("every loop of associators is a sum of pentagons and squares.")
    print()
    print("Epistemic status: exact, exhaustive enumeration for n <= 7 (faces for")
    print("n = 5 only). It illustrates, but does not prove, Mac Lane's coherence")
    print("theorem, which says every diagram of associators commutes for every n.")


if __name__ == "__main__":
    main()
