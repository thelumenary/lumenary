"""Compose reflections and watch the four types of plane isometry appear.

Plane isometries are stored in the normal form of the lesson: z -> a z + b
(direct) or z -> a conj(z) + b (opposite), with |a| = 1 and complex numbers
held as pairs of exact fractions. Reflections in random lines (rational
directions and points) are composed k at a time, for k = 1, 2, 3, 4, and every
product is classified by the lesson's criteria: a = 1 (translation or
identity), a != 1 (rotation about b / (1 - a)), and for opposite maps the
vector a conj(b) + b (zero: reflection; non-zero: glide reflection). Each
classification is double-checked against fixed points. Exact arithmetic on
random samples: evidence for the theorem, which the lesson proves.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "transformation_geometry_isometries",
    "title": "Products of reflections: the four types of plane isometry",
    "evidence": ["exact", "experimental"],
    "lessons": ["transformation-geometry"],
    "summary": (
        "Composes random reflections of the plane in exact rational arithmetic, "
        "using the normal form z -> a z + b or a conj(z) + b, and classifies each "
        "product as identity, translation, rotation, reflection or glide "
        "reflection, checking fixed points. Even products are always direct, odd "
        "ones opposite, and three random mirrors almost always give a glide."
    ),
    "packages": [],
}

ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))


def cadd(z, w):
    """Sum of two complex numbers given as (re, im) pairs."""
    return (z[0] + w[0], z[1] + w[1])


def csub(z, w):
    """Difference z - w."""
    return (z[0] - w[0], z[1] - w[1])


def cmul(z, w):
    """Product z w."""
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def cdiv(z, w):
    """Quotient z / w (w non-zero)."""
    n = w[0] * w[0] + w[1] * w[1]
    return ((z[0] * w[0] + z[1] * w[1]) / n, (z[1] * w[0] - z[0] * w[1]) / n)


def conj(z):
    """Complex conjugate."""
    return (z[0], -z[1])


def unit_from_slope(t):
    """The rational point ((1 - t^2), 2t) / (1 + t^2) on the unit circle."""
    t = Fraction(t)
    d = 1 + t * t
    return ((1 - t * t) / d, 2 * t / d)


def apply(iso, z):
    """Apply an isometry (a, b, opposite) to the point z."""
    a, b, opp = iso
    return cadd(cmul(a, conj(z) if opp else z), b)


def compose(f, g):
    """The isometry 'first g, then f' in normal form."""
    a1, b1, o1 = f
    a2, b2, o2 = g
    if not o1:
        return (cmul(a1, a2), cadd(cmul(a1, b2), b1), o2)
    return (cmul(a1, conj(a2)), cadd(cmul(a1, conj(b2)), b1), not o2)


def reflection(p, e):
    """Reflection in the line through p whose doubled direction is e = u^2.

    z -> e conj(z - p) + p, i.e. a = e and b = p - e conj(p).
    """
    return (e, csub(p, cmul(e, conj(p))), True)


def classify(iso):
    """Return 'identity', 'translation', 'rotation', 'reflection' or 'glide'."""
    a, b, opp = iso
    if not opp:
        if a == ONE:
            return "identity" if b == ZERO else "translation"
        return "rotation"
    return "reflection" if cadd(cmul(a, conj(b)), b) == ZERO else "glide"


def fixed_point_check(iso):
    """Verify the classification using fixed points; True if consistent."""
    kind = classify(iso)
    a, b, opp = iso
    if kind == "rotation":
        c = cdiv(b, csub(ONE, a))
        return apply(iso, c) == c
    if kind == "reflection":
        mid = (b[0] / 2, b[1] / 2)
        return apply(iso, mid) == mid
    if kind in ("translation", "glide"):
        z = (Fraction(3), Fraction(-7))
        shift = csub(apply(iso, apply(iso, z)), z)
        return shift != ZERO and apply(iso, z) != z
    return apply(iso, (Fraction(2), Fraction(5))) == (2, 5)


def fmt(z):
    """Format a complex number x + y i with exact fractions."""
    sign = "-" if z[1] < 0 else "+"
    return f"{z[0]} {sign} {abs(z[1])}i"


def random_reflection(rng):
    """A reflection in a line with one of a few slopes through a random point."""
    slope = rng.choice([0, 1, 2, Fraction(1, 2), -1, Fraction(-1, 3)])
    p = (Fraction(rng.randint(-5, 5)), Fraction(rng.randint(-5, 5)))
    return reflection(p, unit_from_slope(slope))


def census(rng, k, trials):
    """Classify `trials` products of k random reflections."""
    counts = {}
    consistent = True
    for _ in range(trials):
        iso = random_reflection(rng)
        for _ in range(k - 1):
            iso = compose(random_reflection(rng), iso)
        kind = classify(iso)
        counts[kind] = counts.get(kind, 0) + 1
        consistent = consistent and fixed_point_check(iso)
    return counts, consistent


def main():
    rng = random.Random(1872)
    print("Products of k random reflections (400 samples each, exact):")
    for k in range(1, 5):
        counts, ok = census(rng, k, 400)
        parts = ", ".join(f"{name} {n}" for name, n in sorted(counts.items()))
        print(f"  k = {k}: {parts}")
        print(f"         fixed-point checks consistent: {ok}")
    print()
    s1 = reflection(ZERO, ONE)
    s2 = reflection(ZERO, unit_from_slope(Fraction(1, 2)))
    rot = compose(s2, s1)
    print(f"Mirrors y = 0, then y = x/2: z -> ({fmt(rot[0])}) z")
    print("  = rotation by twice the angle between them (cos 2t = 3/5,")
    print("    sin 2t = 4/5 for tan t = 1/2)")
    v = reflection((Fraction(0), Fraction(0)), unit_from_slope(Fraction(0)))
    w = reflection((Fraction(0), Fraction(1)), unit_from_slope(Fraction(0)))
    vw = compose(w, v)
    print(f"Mirrors y = 0, then y = 1: {classify(vw)} by {fmt(vw[1])}")
    print("Footprints z -> conj(z) + 1:", classify((ONE, ONE, True)))
    print()
    print("Epistemic status: exact rational arithmetic, so every product is")
    print("classified without rounding; but these are random samples, not all")
    print("isometries. The classification theorem is proved in the lesson and")
    print("in Lean.")


if __name__ == "__main__":
    main()
