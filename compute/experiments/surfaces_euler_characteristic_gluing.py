"""Surfaces from gluing the sides of a polygon: chi, orientability, and a census.

A word such as "abAB" describes a polygon whose sides, read in order, are
glued in pairs: a lower-case letter is a side traversed forwards, the matching
capital letter the partner side traversed backwards. The program finds the
vertex classes after gluing (V), counts edges (E) and faces (F = 1), computes
chi = V - E + F, decides orientability (a surface word is orientable exactly
when every letter occurs once forwards and once backwards), and names the
surface using the classification theorem. Then it glues the sides of a 2n-gon
in every orientable way and counts the results by genus; the genus-0 counts
are the Catalan numbers. Exact and exhaustive, but only for finitely many n.
"""

import itertools
from math import comb

EXPERIMENT = {
    "id": "surfaces_euler_characteristic_gluing",
    "title": "Gluing polygons into surfaces: chi, orientability and genus",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["surfaces-euler-characteristic"],
    "summary": (
        "Computes V, E, F, the Euler characteristic and orientability of surfaces "
        "given by edge words such as abAB (torus) and abab (projective plane), "
        "names them by the classification theorem, then glues a 2n-gon in all "
        "(2n-1)!! orientable ways for n <= 5 and counts the surfaces by genus, "
        "recovering the Catalan numbers for the spheres."
    ),
    "packages": [],
}


def sides(word):
    """List of (letter, +1/-1) for a word like 'abAB'."""
    return [(ch.lower(), 1 if ch.islower() else -1) for ch in word]


def vertex_count(word):
    """Number of vertex classes after gluing the sides of the polygon.

    Corner i sits at the start of side i. Gluing side i to its partner j
    identifies the start and end of side i with the corresponding ends of
    side j (swapped when the two sides run in the same direction).
    """
    s = sides(word)
    n = len(s)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        parent[find(x)] = find(y)

    positions = {}
    for i, (letter, _) in enumerate(s):
        positions.setdefault(letter, []).append(i)
    for letter, (i, j) in positions.items():
        tail_i, head_i = (i, (i + 1) % n)
        tail_j, head_j = (j, (j + 1) % n)
        if s[i][1] == -1:
            tail_i, head_i = head_i, tail_i
        if s[j][1] == -1:
            tail_j, head_j = head_j, tail_j
        union(tail_i, tail_j)
        union(head_i, head_j)
    return len({find(x) for x in range(n)})


def is_orientable(word):
    """Each letter appears once with each exponent."""
    s = sides(word)
    return all(sorted(e for l, e in s if l == letter) == [-1, 1]
               for letter in {l for l, _ in s})


def euler_characteristic(word):
    """chi = V - E + F for the one-polygon surface given by the word."""
    return vertex_count(word) - len(word) // 2 + 1


def name(chi, orientable):
    """Name a closed connected surface by the classification theorem."""
    if orientable:
        g = (2 - chi) // 2
        return {0: "sphere", 1: "torus"}.get(g, f"orientable, genus {g}")
    k = 2 - chi
    return {1: "projective plane", 2: "Klein bottle"}.get(
        k, f"sum of {k} projective planes")


def pairings(items):
    """All perfect matchings of a list of even length."""
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for k in range(len(rest)):
        for m in pairings(rest[:k] + rest[k + 1:]):
            yield [(first, rest[k])] + m


def genus_census(n):
    """{genus: count} over all orientable gluings of a 2n-gon."""
    counts = {}
    letters = "abcdefghij"
    for matching in pairings(list(range(2 * n))):
        word = [""] * (2 * n)
        for k, (i, j) in enumerate(matching):
            word[i], word[j] = letters[k], letters[k].upper()
        w = "".join(word)
        g = (2 - euler_characteristic(w)) // 2
        counts[g] = counts.get(g, 0) + 1
    return counts


def catalan(n):
    """The n-th Catalan number."""
    return comb(2 * n, n) // (n + 1)


def main():
    examples = ["aA", "abAB", "abAb", "abab", "aabb", "abcABC",
                "abABcdCD", "abABcc", "aabbcc"]
    print(f"{'word':<10}{'V':>3}{'E':>3}{'F':>3}{'chi':>5}  orientable  surface")
    for w in examples:
        v, e = vertex_count(w), len(w) // 2
        chi = v - e + 1
        o = is_orientable(w)
        print(f"{w:<10}{v:>3}{e:>3}{1:>3}{chi:>5}  {str(o):<10}  {name(chi, o)}")
    print("Note: abABcc (torus # projective plane) has the same chi and")
    print("orientability as aabbcc, so by classification they are the same.")
    print()
    print("All orientable gluings of a 2n-gon, counted by genus:")
    for n in range(1, 6):
        counts = genus_census(n)
        total = sum(counts.values())
        row = ", ".join(f"g{g}: {c}" for g, c in sorted(counts.items()))
        print(f"  n = {n}: {total:>3} gluings; {row};"
              f" Catalan({n}) = {catalan(n)}")
    print()
    print("Epistemic status: exact and exhaustive for the words and the n shown.")
    print("That the genus-0 count is always Catalan (and the Harer-Zagier")
    print("formula for higher genus) is a theorem; this is evidence for n <= 5.")


if __name__ == "__main__":
    main()
