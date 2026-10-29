"""Klein's Erlangen programme as a table: which quantities does each group keep?

Four groups of plane transformations, from small to large: Euclidean motions,
similarities, affine maps and projective maps (in homogeneous coordinates).
For random configurations of rational points the experiment applies random
members of each group, in exact fraction arithmetic, and tests whether a
quantity is unchanged: distance, angle, ratio of two lengths, parallelism,
ratio along a line, collinearity and the cross-ratio of four collinear points.
The larger the group, the fewer invariants survive. These are exact checks on
random samples: a "kept in 100 of 100" is evidence, the lesson has the proofs.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "transformation_geometry_erlangen",
    "title": "Invariants of the Euclidean, similarity, affine and projective groups",
    "evidence": ["exact", "experimental", "counterexample"],
    "lessons": ["transformation-geometry"],
    "summary": (
        "Applies random Euclidean, similarity, affine and projective maps to "
        "random rational configurations in exact arithmetic and records which of "
        "seven quantities (distance, angle, length ratio, parallelism, ratio along "
        "a line, collinearity, cross-ratio) are preserved. Failures are genuine "
        "counterexamples; successes are evidence for the invariance theorems."
    ),
    "packages": [],
}


def rational_rotation(rng):
    """(c, s) with c^2 + s^2 = 1, from a random rational slope."""
    t = Fraction(rng.randint(-6, 6), rng.randint(1, 6))
    d = 1 + t * t
    return (1 - t * t) / d, 2 * t / d


def random_map(rng, group):
    """A random 3 x 3 matrix (homogeneous coordinates) from the group."""
    tx, ty = Fraction(rng.randint(-5, 5)), Fraction(rng.randint(-5, 5))
    if group in ("euclidean", "similarity"):
        c, s = rational_rotation(rng)
        k = 1 if group == "euclidean" else Fraction(rng.choice([1, 3, 4, 6]), 2)
        flip = rng.choice([1, -1])
        return [[k * c, -k * s * flip, tx], [k * s, k * c * flip, ty], [0, 0, 1]]
    while True:
        m = [[Fraction(rng.randint(-4, 4)) for _ in range(3)] for _ in range(3)]
        if group == "affine":
            m[2] = [Fraction(0), Fraction(0), Fraction(1)]
            m[0][2], m[1][2] = tx, ty
        if det3(m) != 0:
            return m


def det3(m):
    """Determinant of a 3 x 3 matrix."""
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def act(m, p):
    """Image of the point p, or None if it is sent to infinity."""
    x, y = p
    u = [m[i][0] * x + m[i][1] * y + m[i][2] for i in range(3)]
    return None if u[2] == 0 else (u[0] / u[2], u[1] / u[2])


def sub(p, q):
    """The vector from q to p."""
    return (p[0] - q[0], p[1] - q[1])


def dot(u, v):
    """Dot product."""
    return u[0] * v[0] + u[1] * v[1]


def cross(u, v):
    """2D cross product; zero exactly when u and v are parallel."""
    return u[0] * v[1] - u[1] * v[0]


def param(a, b, c):
    """t with c = a + t (b - a), for collinear points a != b."""
    d = sub(b, a)
    k = 0 if d[0] != 0 else 1
    return sub(c, a)[k] / d[k]


def cross_ratio(a, b, c, d):
    """(a, b; c, d) = (c - a)(d - b) / ((c - b)(d - a)) for numbers."""
    return (c - a) * (d - b) / ((c - b) * (d - a))


def angle_key(a, o, b):
    """(sign of cos, cos^2) of the angle aob: equal keys = equal angles."""
    u, v = sub(a, o), sub(b, o)
    d = dot(u, v)
    return (d > 0) - (d < 0), d * d / (dot(u, u) * dot(v, v))


def quantities(pts):
    """The seven quantities for a configuration (a, b, c, d, e, f, g, h).

    a, b, c, d are collinear (on a line), e, f, g are a triangle, and h is
    chosen so that e h is parallel to f g.
    """
    a, b, c, d, e, f, g, h = pts
    return {
        "distance": dot(sub(e, f), sub(e, f)),
        "angle": angle_key(f, e, g),
        "length ratio": dot(sub(e, f), sub(e, f)) / dot(sub(f, g), sub(f, g)),
        "parallelism": cross(sub(h, e), sub(g, f)) == 0,
        "ratio on a line": param(a, b, c),
        "collinearity": cross(sub(b, a), sub(c, a)) == 0,
        "cross-ratio": cross_ratio(*(param(a, b, x) for x in (a, b, c, d))),
    }


def random_configuration(rng):
    """Eight rational points with the incidences described in quantities()."""
    def pt():
        return (Fraction(rng.randint(-6, 6)), Fraction(rng.randint(-6, 6)))
    a = pt()
    b = (a[0] + rng.randint(1, 3), a[1] + rng.randint(-3, 3))
    c, d = (tuple(a[i] + t * (b[i] - a[i]) for i in range(2))
            for t in (Fraction(3), Fraction(-2, 3)))
    e, f = pt(), pt()
    while f == e:
        f = pt()
    g = pt()
    while cross(sub(f, e), sub(g, e)) == 0:
        g = pt()
    h = (e[0] + 2 * (g[0] - f[0]), e[1] + 2 * (g[1] - f[1]))
    return (a, b, c, d, e, f, g, h)


def survival(rng, group, trials):
    """For each quantity, in how many trials it was preserved."""
    kept = {}
    done = 0
    while done < trials:
        pts = random_configuration(rng)
        m = random_map(rng, group)
        image = [act(m, p) for p in pts]
        if None in image or len(set(image[:4])) < 4:
            continue
        before, after = quantities(pts), quantities(image)
        for name in before:
            kept[name] = kept.get(name, 0) + (before[name] == after[name])
        done += 1
    return kept


def main():
    rng = random.Random(1872)
    groups = ["euclidean", "similarity", "affine", "projective"]
    trials = 100
    table = {g: survival(rng, g, trials) for g in groups}
    print(f"Quantities kept in {trials} random trials (exact arithmetic)")
    print(f"{'':16}" + "".join(f"{g[:10]:>11}" for g in groups))
    for name in table["euclidean"]:
        row = "".join(f"{table[g][name]:>11}" for g in groups)
        print(f"{name:16}{row}")
    print()
    print("Each larger group keeps fewer invariants: Euclidean motions keep")
    print("distance; similarities keep angles and ratios of lengths; affine")
    print("maps keep parallelism and ratios along a line; projective maps keep")
    print("only incidence (collinearity) and the cross-ratio.")
    print()
    print("Epistemic status: exact computation on random samples. A count")
    print("below 100 exhibits genuine counterexamples (the quantity is not")
    print("invariant); a count of 100 is evidence, and the lesson proves it.")


if __name__ == "__main__":
    main()
