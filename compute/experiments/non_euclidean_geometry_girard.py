"""Spherical triangles: angle excess versus area, three independent ways.

For triangles on the unit sphere the experiment computes (1) the angle excess
alpha + beta + gamma - pi from the angles between the planes of the sides,
(2) the area by Monte Carlo: the fraction of 200,000 random points of the
sphere that fall inside the triangle, times 4 pi, with a standard error, and
(3) the area from the exact Van Oosterom-Strackee formula
tan(E/2) = |A.(B x C)| / (1 + A.B + B.C + C.A). Girard's theorem says all three
agree. It also checks the spherical law of cosines on each triangle. The angle
and formula columns are numerical (floating point); the Monte Carlo column is
statistical evidence, with its uncertainty shown.
"""

import numpy as np

EXPERIMENT = {
    "id": "non_euclidean_geometry_girard",
    "title": "Girard's theorem: angle excess equals area on the sphere",
    "evidence": ["numerical", "statistical"],
    "lessons": ["non-euclidean-geometry"],
    "summary": (
        "For several spherical triangles, compares the angle excess with the area "
        "estimated by Monte Carlo sampling of 200,000 random points (with standard "
        "error) and with an exact closed formula, and checks the spherical law of "
        "cosines. Agreement within sampling error is evidence for Girard's theorem, "
        "which the lesson proves."
    ),
    "packages": ["numpy"],
}


def unit(v):
    """The vector v scaled to length 1."""
    v = np.asarray(v, dtype=float)
    return v / np.linalg.norm(v)


def from_lat_lon(lat, lon):
    """Unit vector at latitude, longitude given in degrees."""
    la, lo = np.radians(lat), np.radians(lon)
    return np.array([np.cos(la) * np.cos(lo), np.cos(la) * np.sin(lo), np.sin(la)])


def vertex_angle(a, b, c):
    """The angle at a between the great circles ab and ac."""
    n1, n2 = np.cross(a, b), np.cross(a, c)
    cos_t = np.dot(n1, n2) / (np.linalg.norm(n1) * np.linalg.norm(n2))
    return float(np.arccos(np.clip(cos_t, -1.0, 1.0)))


def angle_excess(a, b, c):
    """alpha + beta + gamma - pi."""
    return vertex_angle(a, b, c) + vertex_angle(b, c, a) + \
        vertex_angle(c, a, b) - np.pi


def exact_area(a, b, c):
    """Van Oosterom-Strackee: the solid angle of the triangle abc."""
    num = abs(np.dot(a, np.cross(b, c)))
    den = 1 + np.dot(a, b) + np.dot(b, c) + np.dot(c, a)
    return float(2 * np.arctan2(num, den))


def monte_carlo_area(a, b, c, n, rng):
    """(estimate, standard error) of the area from n random sphere points."""
    p = rng.normal(size=(n, 3))
    p /= np.linalg.norm(p, axis=1)[:, None]
    inside = np.ones(n, dtype=bool)
    for u, v, w in ((a, b, c), (b, c, a), (c, a, b)):
        normal = np.cross(u, v)
        inside &= np.sign(p @ normal) == np.sign(np.dot(w, normal))
    frac = inside.mean()
    return 4 * np.pi * frac, 4 * np.pi * np.sqrt(frac * (1 - frac) / n)


def law_of_cosines_gap(a, b, c):
    """|cos(side ab) - (cos ac cos bc + sin ac sin bc cos gamma)|."""
    side = {k: np.arccos(np.clip(np.dot(*v), -1, 1)) for k, v in
            {"ab": (a, b), "ac": (a, c), "bc": (b, c)}.items()}
    gamma = vertex_angle(c, a, b)
    rhs = np.cos(side["ac"]) * np.cos(side["bc"]) + \
        np.sin(side["ac"]) * np.sin(side["bc"]) * np.cos(gamma)
    return float(abs(np.cos(side["ab"]) - rhs))


TRIANGLES = {
    "octant (3 right angles)": ((90, 0), (0, 0), (0, 90)),
    "Mexico City-B. Aires-Lagos": ((19.4, -99.1), (-34.6, -58.4), (6.5, 3.4)),
    "Mumbai-Beijing-Jakarta": ((19.1, 72.9), (39.9, 116.4), (-6.2, 106.8)),
    "thin: Cairo-Lagos-Dakar": ((30.0, 31.2), (6.5, 3.4), (14.7, -17.5)),
    "Sydney-Lima-Tokyo": ((-33.9, 151.2), (-12.0, -77.0), (35.7, 139.7)),
    "small: 1 degree sides": ((0, 0), (0, 1), (1, 0)),
}


def main():
    rng = np.random.default_rng(1829)
    print(f"{'triangle':<27}{'excess':>9}{'exact':>9}{'Monte Carlo':>18}"
          f"{'cos law':>9}")
    for label, pts in TRIANGLES.items():
        a, b, c = (from_lat_lon(*p) for p in pts)
        ex = angle_excess(a, b, c)
        area = exact_area(a, b, c)
        mc, se = monte_carlo_area(a, b, c, 200_000, rng)
        gap = law_of_cosines_gap(a, b, c)
        print(f"{label:<27}{ex:9.5f}{area:9.5f}{mc:10.4f} +- {se:.4f}"
              f"{gap:9.1e}")
    print()
    print("Areas on the unit sphere (4 pi = 12.566 is the whole sphere). The")
    print("octant has excess pi/2 and area 1/8 of the sphere. Small triangles")
    print("are almost flat: their angle sum is barely above pi.")
    print("A Monte Carlo value within about 2 standard errors of the exact")
    print("area is what sampling theory predicts.")
    print()
    print("Epistemic status: the excess and the exact formula are floating-")
    print("point computations; the Monte Carlo column is statistical evidence")
    print("with its error bar. Six triangles do not prove Girard's theorem;")
    print("the lesson does. 'cos law' is the residual of the law of cosines.")


if __name__ == "__main__":
    main()
