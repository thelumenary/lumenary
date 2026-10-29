"""R(3, 3) = 6 by exhaustive search, Goodman's count, and Erdos's random bound.

A red-blue colouring of the 15 edges of K6 is a 15-bit number, so there are
2^15 = 32768 colourings. We check every one for a monochromatic triangle,
count the fewest monochromatic triangles any colouring can have (Goodman
proved in 1959 that it is 2 for K6), and list the colourings of K5 with no
monochromatic triangle. This exhaustive check is a complete proof of
R(3, 3) = 6, provided the code is right.

For larger k exhaustive search is hopeless (K18 has 153 edges). Erdos's 1947
argument instead shows that a *random* colouring of K_n has, on average,
fewer than one monochromatic K_k when C(n, k) * 2^(1 - C(k, 2)) < 1, so some
colouring has none and R(k, k) > n. We tabulate the n this gives.
"""

import itertools
import math

EXPERIMENT = {
    "id": "graph_theory_ramsey",
    "title": "Ramsey numbers: exhaustive search for R(3, 3) and Erdos's bound",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["graph-theory"],
    "summary": (
        "Checks all 32768 red-blue colourings of K6 for monochromatic triangles "
        "(every one has at least two, as Goodman's theorem says), finds the 12 "
        "colourings of K5 with none, and tabulates the lower bounds for R(k, k) "
        "given by Erdos's probabilistic counting argument. The exhaustive part is "
        "a computer proof of R(3, 3) = 6, as far as the code is correct."
    ),
    "packages": [],
}


def edge_index(n):
    """Map each edge (a, b), a < b, of K_n to a bit position."""
    return {e: k for k, e in enumerate(itertools.combinations(range(n), 2))}


def triangle_masks(n):
    """Bit masks of the three edges of each triangle of K_n."""
    idx = edge_index(n)
    return [(1 << idx[(a, b)]) | (1 << idx[(a, c)]) | (1 << idx[(b, c)])
            for a, b, c in itertools.combinations(range(n), 3)]


def mono_triangles(colouring, masks):
    """Number of triangles whose edges are all red (bit 1) or all blue (0)."""
    return sum(1 for m in masks if colouring & m in (0, m))


def census(n):
    """Monochromatic-triangle counts of all 2^C(n,2) colourings of K_n."""
    masks = triangle_masks(n)
    return [mono_triangles(c, masks) for c in range(1 << math.comb(n, 2))]


def red_graph_is_five_cycle(colouring):
    """For K5: is the red graph a 5-cycle (connected and 2-regular)?"""
    idx = edge_index(5)
    red = [e for e, k in idx.items() if colouring >> k & 1]
    degree = [sum(v in e for e in red) for v in range(5)]
    if len(red) != 5 or any(d != 2 for d in degree):
        return False
    seen, todo = {0}, [0]
    while todo:
        v = todo.pop()
        for a, b in red:
            w = b if a == v else a if b == v else None
            if w is not None and w not in seen:
                seen.add(w)
                todo.append(w)
    return len(seen) == 5


def erdos_bound(k):
    """Largest n with C(n, k) * 2^(1 - C(k, 2)) < 1, so that R(k, k) > n."""
    n = k
    while math.comb(n + 1, k) * 2 < 2 ** math.comb(k, 2):
        n += 1
    return n


def main():
    six = census(6)
    print(f"K6: {len(six)} colourings of 15 edges")
    print(f"  with no monochromatic triangle: {six.count(0)}")
    print(f"  fewest monochromatic triangles: {min(six)} "
          f"(attained by {six.count(min(six))} colourings)")
    five = census(5)
    good = [c for c, t in enumerate(five) if t == 0]
    print(f"K5: {len(five)} colourings; with no monochromatic triangle: "
          f"{len(good)}")
    print(f"  red graph a 5-cycle in each of them: "
          f"{all(red_graph_is_five_cycle(c) for c in good)}")
    print("So R(3, 3) = 6: K6 always has a monochromatic triangle, K5 need not.")
    print()
    print("Erdos (1947): a random colouring shows R(k, k) > n for these n")
    print("   k   n (Erdos)   2^(k/2)   known R(k, k)")
    known = {3: "6", 4: "18", 5: "43 to 46"}
    for k in range(3, 11):
        print(f"{k:>4} {erdos_bound(k):>11} {2 ** (k / 2):>9.1f}   "
              f"{known.get(k, 'not known')}")
    print()
    print("Epistemic status: the K5 and K6 results are exact and exhaustive, "
          "so they\nprove R(3, 3) = 6 and Goodman's minimum for K6, assuming "
          "this code is\ncorrect. The Erdos column is exact arithmetic for a "
          "proved bound; the\n'known' column is quoted from the literature, "
          "not computed here.")


if __name__ == "__main__":
    main()
