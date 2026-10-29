"""Counting up to symmetry: necklaces, bracelets and coloured cubes.

Two colourings are "the same" if a symmetry carries one to the other, so we
are counting orbits of a group acting on colourings. We count orbits in two
independent ways and compare:

* brute force: list all colourings and pick one canonical representative
  (the smallest) from each orbit;
* Burnside's lemma: average the number of colourings fixed by each group
  element, which for necklaces gives (1/n) sum_{d | n} phi(d) k^(n/d), and
  for the cube is Polya's cycle-index polynomial evaluated at k colours.

We also show why the naive count k^n / n is wrong: symmetric colourings
have smaller orbits. The checks are exhaustive for the sizes shown.
"""

import itertools
from fractions import Fraction
from math import gcd

EXPERIMENT = {
    "id": "enumerative_combinatorics_burnside",
    "title": "Necklaces, bracelets and cubes: brute force versus Burnside",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["enumerative-combinatorics"],
    "summary": (
        "Counts necklaces (rotations) and bracelets (rotations and reflections) "
        "with n <= 9 beads in 2 or 3 colours, and face colourings of a cube under "
        "its 24 rotations, both by brute-force orbit enumeration and by Burnside's "
        "lemma, and shows that the naive count k^n/n is wrong. Exhaustive for "
        "these sizes."
    ),
    "packages": [],
}


def phi(n):
    """Euler's totient function."""
    return sum(1 for a in range(1, n + 1) if gcd(a, n) == 1)


def rotations(n):
    """The n rotations of an n-bead necklace, as position permutations."""
    return [tuple((i + r) % n for i in range(n)) for r in range(n)]


def dihedral(n):
    """Rotations and reflections: the dihedral group of order 2n."""
    return rotations(n) + [tuple((r - i) % n for i in range(n)) for r in range(n)]


def act(perm, colouring):
    """The colouring moved by a permutation of positions."""
    return tuple(colouring[perm[i]] for i in range(len(perm)))


def orbits_brute_force(group, k, size):
    """Number of orbits: count colourings that are smallest in their orbit."""
    return sum(1 for c in itertools.product(range(k), repeat=size)
               if all(c <= act(g, c) for g in group))


def cycles(perm):
    """Number of cycles of a permutation."""
    seen, count = set(), 0
    for start in range(len(perm)):
        if start not in seen:
            count += 1
            i = start
            while i not in seen:
                seen.add(i)
                i = perm[i]
    return count


def orbits_burnside(group, k):
    """Burnside: average of |Fix g|; a permutation with c cycles fixes k^c."""
    total = sum(k ** cycles(g) for g in group)
    return Fraction(total, len(group))


def necklace_formula(n, k):
    """(1/n) sum over divisors d of n of phi(d) k^(n/d)."""
    return Fraction(sum(phi(d) * k ** (n // d) for d in range(1, n + 1)
                        if n % d == 0), n)


def cube_rotations():
    """The 24 rotations of a cube acting on its faces U, D, F, B, L, R."""
    spin = (0, 1, 5, 4, 2, 3)   # quarter turn about the U-D axis
    tilt = (2, 3, 1, 0, 4, 5)   # quarter turn about the L-R axis
    group, frontier = {tuple(range(6))}, [tuple(range(6))]
    while frontier:
        g = frontier.pop()
        for h in (spin, tilt):
            gh = tuple(g[h[i]] for i in range(6))
            if gh not in group:
                group.add(gh)
                frontier.append(gh)
    return sorted(group)


def main():
    print("Necklaces of n beads in k colours (rotations only):")
    print("   n  k   brute force   Burnside   formula   naive k^n/n")
    for n, k in [(4, 2), (6, 2), (6, 3), (8, 2), (9, 2), (9, 3)]:
        group = rotations(n)
        brute = orbits_brute_force(group, k, n)
        burn = orbits_burnside(group, k)
        naive = Fraction(k ** n, n)
        print(f"{n:>4} {k:>2} {brute:>13} {str(burn):>10} "
              f"{str(necklace_formula(n, k)):>9} {float(naive):>13.2f}")
    print("Bracelets (rotations and reflections), k = 2:")
    for n in (4, 6, 8, 9):
        group = dihedral(n)
        print(f"   n = {n}: brute force {orbits_brute_force(group, 2, n)}, "
              f"Burnside {orbits_burnside(group, 2)}")
    print()
    cube = cube_rotations()
    types = sorted(cycles(g) for g in cube)
    print(f"Cube: {len(cube)} rotations generated from two quarter turns.")
    print(f"  number with c cycles on the faces, c = 1..6: "
          f"{[types.count(c) for c in range(1, 7)]}")
    for k in (2, 3):
        print(f"  face colourings with {k} colours up to rotation: brute force "
              f"{orbits_brute_force(cube, k, 6)}, Burnside "
              f"{orbits_burnside(cube, k)}")
    print()
    print("Epistemic status: exact and exhaustive for every size shown - each "
          "count\nwas obtained by listing all colourings and agrees with "
          "Burnside's lemma.\nThat is evidence for the formulas at these sizes; "
          "the lemma itself is\nproved in the lesson (and in Mathlib).")


if __name__ == "__main__":
    main()
