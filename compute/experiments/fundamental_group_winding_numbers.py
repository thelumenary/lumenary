"""Winding numbers by path lifting, and what they can prove.

A loop in the punctured plane C minus {0} is lifted to the covering map
R -> circle by following its angle continuously: between two nearby samples
the angle changes by the representative of the difference in (-pi, pi].
The winding number is the total change divided by 2 pi. We compare it with
the contour integral (1 / 2 pi i) times the integral of dz / z, computed
separately by the midpoint rule. Then we watch a homotopy of circles: the
winding number stays constant until the circle passes through 0. Finally we
apply the idea to a cubic: the image of a large circle winds 3 times around
0 and the image of a small one 0 times, so the cubic must vanish somewhere
in between. Evidence: numerical (sampled loops), not proof.
"""

import cmath
import math

EXPERIMENT = {
    "id": "fundamental_group_winding_numbers",
    "title": "Winding numbers by lifting loops to the real line",
    "evidence": ["numerical"],
    "lessons": ["fundamental-group"],
    "summary": (
        "Lifts sampled loops in the punctured plane to the real line by "
        "following the angle continuously, and compares the winding number "
        "with a separate midpoint-rule contour integral. It shows that the "
        "winding number is constant along a homotopy until the loop crosses "
        "0, and that a cubic's image of circles winds 0 times for small and 3 "
        "times for large radii, forcing a root. Numerical evidence only."
    ),
    "packages": [],
}

SAMPLES = 2000


def sample(loop, n=SAMPLES):
    """Points loop(k / n) for k = 0..n (the last equals the first)."""
    return [loop(k / n) for k in range(n + 1)]


def lift_angles(points, centre=0j):
    """Continuous lift of the angle of points - centre (path lifting).

    Raises ValueError if the loop passes through the centre.
    """
    angles = []
    for z in points:
        w = z - centre
        if abs(w) < 1e-12:
            raise ValueError("the loop passes through the centre")
        a = cmath.phase(w)
        if angles:
            step = (a - angles[-1] + math.pi) % (2 * math.pi) - math.pi
            a = angles[-1] + step
        angles.append(a)
    return angles


def winding_number(points, centre=0j):
    """(final angle - initial angle) / 2 pi of the lifted loop."""
    angles = lift_angles(points, centre)
    return (angles[-1] - angles[0]) / (2 * math.pi)


def contour_integral(points, centre=0j):
    """(1 / 2 pi i) * integral of dz / (z - centre), by the midpoint rule."""
    total = 0j
    for z0, z1 in zip(points, points[1:]):
        total += (z1 - z0) / ((z0 + z1) / 2 - centre)
    return total / (2j * math.pi)


def circle(radius=1.0, centre=0j, turns=1):
    """The loop t -> centre + radius * exp(2 pi i turns t)."""
    return lambda t: centre + radius * cmath.exp(2j * math.pi * turns * t)


def cubic(z):
    """p(z) = z^3 - 2z + 2, a cubic with no root on |z| = 1 or |z| = 2."""
    return z ** 3 - 2 * z + 2


def main():
    loops = [
        ("unit circle", circle()),
        ("circle, twice round", circle(turns=2)),
        ("circle, backwards", circle(turns=-1)),
        ("circle around 3", circle(1.0, 3 + 0j)),
        ("ellipse 3x by 0.5y", lambda t: complex(3 * math.cos(2 * math.pi * t),
                                               0.5 * math.sin(2 * math.pi * t))),
    ]
    print("Loop around 0            lift (turns)   contour integral")
    for name, loop in loops:
        pts = sample(loop)
        w, c = winding_number(pts), contour_integral(pts)
        print(f"  {name:<22} {w:10.6f}     {c.real:9.6f} {c.imag:+.1e}i")
    print()
    print("Homotopy of circles: radius 1, centre s (crosses 0 at s = 1)")
    row = []
    for s in (0.0, 0.5, 0.9, 1.0, 1.1, 1.5):
        try:
            w = winding_number(sample(circle(1.0, complex(s, 0))))
            row.append(f"s={s}: {round(w)}")
        except ValueError:
            row.append(f"s={s}: undefined")
    print("  " + ", ".join(row))
    print()
    print("Images of circles |z| = R under p(z) = z^3 - 2z + 2:")
    row = []
    for radius in (0.5, 1.0, 1.5, 2.0, 10.0):
        pts = [cubic(z) for z in sample(circle(radius))]
        row.append(f"R={radius}: {round(winding_number(pts))}")
    print("  " + ", ".join(row))
    roots = sorted(abs(r) for r in (-1.7693, 0.8846 + 0.5897j))
    print(f"  (the roots have absolute values about {roots[0]:.3f} (twice) and")
    print(f"  {roots[1]:.3f}; by the argument principle the winding number")
    print("  counts the roots inside the circle)")
    print()
    print("If p had no root, the loops p(R e^{2 pi i t}) would be homotopic in")
    print("C minus {0} for all R, so they would all wind equally often. Winding")
    print("0 times for small R and 3 times for large R forces a root.")
    print()
    print("Epistemic status: numerical. Each loop is sampled at 2000 points, and")
    print("the lift is right only if consecutive samples turn by less than pi;")
    print("the agreement with the contour integral is a consistency check, not")
    print("a proof. The theorems behind it (pi_1(S^1) = Z and homotopy")
    print("invariance) are proved in the lesson.")


if __name__ == "__main__":
    main()
