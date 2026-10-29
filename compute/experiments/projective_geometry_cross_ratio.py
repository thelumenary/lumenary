"""The cross-ratio: invariant under every projective map of the line.

Points of the projective line are stored as homogeneous pairs [x : y] of exact
fractions, so the point at infinity [1 : 0] needs no special treatment. With
the bracket [p q] = p_x q_y - p_y q_x, the cross-ratio is

    (a, b; c, d) = [a c][b d] / ([a d][b c]),

which agrees with ((a - c)(b - d)) / ((a - d)(b - c)) for finite points. The
program applies seeded random Moebius transformations x -> (ax + b)/(cx + d)
(2 x 2 matrices with non-zero determinant) to random quadruples and checks
the cross-ratio exactly, while the simple ratio (a - c)/(b - c) changes. It
lists the six values taken by the cross-ratio under the 24 orderings, and uses
invariance to locate a fence post in a perspective photograph.

All arithmetic is exact: a finite exhaustive check of the cases listed.
"""

import random
from fractions import Fraction
from itertools import permutations

EXPERIMENT = {
    "id": "projective_geometry_cross_ratio",
    "title": "The cross-ratio under projective maps, exactly",
    "evidence": ["exact", "experimental"],
    "lessons": ["projective-geometry"],
    "summary": (
        "Works with homogeneous coordinates on the projective line in exact "
        "rational arithmetic: checks that 300 seeded random Moebius maps preserve "
        "the cross-ratio of random quadruples (including the point at infinity) "
        "while ratios of lengths change, lists the six values under the 24 "
        "orderings, and predicts a fence post's position in a perspective photo."
    ),
    "packages": [],
}

INFINITY = (Fraction(1), Fraction(0))


def point(x):
    """The homogeneous pair [x : 1] of a finite point."""
    return (Fraction(x), Fraction(1))


def bracket(p, q):
    """The 2 x 2 determinant [p q] = p_x q_y - p_y q_x."""
    return p[0] * q[1] - p[1] * q[0]


def cross_ratio(a, b, c, d):
    """(a, b; c, d) = [a c][b d] / ([a d][b c]) for homogeneous pairs."""
    return (bracket(a, c) * bracket(b, d)) / (bracket(a, d) * bracket(b, c))


def apply(m, p):
    """Apply the 2 x 2 matrix m = ((a, b), (c, d)) to the homogeneous pair p."""
    (a, b), (c, d) = m
    return (a * p[0] + b * p[1], c * p[0] + d * p[1])


def affine(p):
    """The affine coordinate x/y of [x : y], or None for the point at infinity."""
    return None if p[1] == 0 else p[0] / p[1]


def random_mobius(rng):
    """A random integer 2 x 2 matrix with non-zero determinant."""
    while True:
        m = tuple(tuple(Fraction(rng.randint(-9, 9)) for _ in range(2))
                  for _ in range(2))
        if m[0][0] * m[1][1] - m[0][1] * m[1][0] != 0:
            return m


def six_values(lam):
    """The values of the cross-ratio over all 24 orderings of four points.

    The points lam, 1, 0, infinity have cross-ratio (lam, 1; 0, inf) = lam.
    """
    base = [point(lam), point(1), point(0), INFINITY]
    values = {cross_ratio(*[base[i] for i in perm])
              for perm in permutations(range(4))}
    return sorted(values)


def fourth_point(a, b, c, lam):
    """The affine x with ((a - c)(b - x)) / ((a - x)(b - c)) = lam.

    Clearing denominators gives b - x = k (a - x) with k = lam (b - c)/(a - c).
    """
    k = lam * (b - c) / (a - c)
    return (k * a - b) / (k - 1)


def photo(x):
    """Position in a perspective photo of a point x metres along the fence."""
    return Fraction(x) / (x + 2)


def main():
    rng = random.Random(2024)
    trials, invariant, ratio_changed = 300, 0, 0
    for _ in range(trials):
        xs = rng.sample(range(-20, 21), 4)
        quad = [point(x) for x in xs]
        if rng.random() < 0.25:
            quad[rng.randrange(4)] = INFINITY
        m = random_mobius(rng)
        images = [apply(m, p) for p in quad]
        if any(bracket(images[i], images[j]) == 0
               for i in range(4) for j in range(i)):
            continue
        invariant += cross_ratio(*images) == cross_ratio(*quad)
        a, b, c = (affine(p) for p in quad[:3])
        a2, b2, c2 = (affine(p) for p in images[:3])
        if None not in (a, b, c, a2, b2, c2):
            ratio_changed += (a - c) / (b - c) != (a2 - c2) / (b2 - c2)
    print(f"{trials} random Moebius maps on random quadruples (exact):")
    print(f"   cross-ratio unchanged in {invariant} of {trials} cases")
    print(f"   simple ratio (a - c)/(b - c) changed in {ratio_changed} cases")
    print()
    for lam in (Fraction(3), Fraction(-1)):
        vals = six_values(lam)
        print(f"orderings of four points with cross-ratio {lam}: "
              f"{len(vals)} values")
        print("   " + ", ".join(str(v) for v in vals))
    print()
    posts = [0, 1, 2, 3]
    cr_ground = cross_ratio(*[point(x) for x in posts])
    seen = [photo(x) for x in posts[:3]]
    print("Fence posts 1 m apart at 0, 1, 2, 3 have cross-ratio", cr_ground)
    print("In the photo (x -> x/(x + 2)) the first three appear at",
          ", ".join(str(s) for s in seen))
    x = fourth_point(*seen, cr_ground)
    print(f"Invariance predicts the fourth at {x}; the photo has"
          f" {photo(posts[3])}")
    print()
    print("Epistemic status: exact rational arithmetic over finitely many\n"
          "random cases (and two worked examples). This is evidence, not a\n"
          "proof, of invariance; the proof is the algebra in the lesson,\n"
          "checked in Lean as cross_ratio_mobius.")


if __name__ == "__main__":
    main()
