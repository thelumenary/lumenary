"""Measure inscribed angles on a circle and compare them with the theorem.

The inscribed angle theorem predicts that every point P on the major arc of a
chord AB sees AB under half the central angle, and every point on the minor
arc under 180 degrees minus that. We place thousands of seeded random points
on each arc, measure the angle APB in floating point and report the largest
deviation from the prediction. Points inside or outside the circle see the
chord under a larger or smaller angle, which illustrates the converse.
This is numerical evidence for finitely many points, not a proof.
"""

import math
import random

EXPERIMENT = {
    "id": "euclidean_geometry_inscribed_angles",
    "title": "Inscribed angles, measured",
    "evidence": ["numerical", "experimental"],
    "lessons": ["euclidean-geometry"],
    "summary": (
        "Measures the angle APB for 2,000 seeded random points P on each arc of "
        "a chord AB of the unit circle and compares it with the inscribed angle "
        "theorem (half the central angle, or 180 degrees minus that), including "
        "Thales' case of a diameter and points off the circle. Floating-point "
        "evidence for finitely many points; the proof is in the lesson."
    ),
    "packages": [],
}


def point_on_circle(degrees, radius=1.0):
    """The point at the given angle (degrees) on the circle about the origin."""
    t = math.radians(degrees)
    return (radius * math.cos(t), radius * math.sin(t))


def angle_at(p, q, r):
    """The angle PQR at the vertex q, in degrees, between 0 and 180.

    Uses atan2(|cross|, dot), which stays accurate for angles near 0 and 180.
    """
    ux, uy = p[0] - q[0], p[1] - q[1]
    vx, vy = r[0] - q[0], r[1] - q[1]
    if (ux, uy) == (0, 0) or (vx, vy) == (0, 0):
        raise ValueError("the vertex must differ from both other points")
    cross = ux * vy - uy * vx
    dot = ux * vx + uy * vy
    return math.degrees(math.atan2(abs(cross), dot))


def arc_samples(start, end, count, rng):
    """`count` random angles (degrees) strictly between start and end."""
    return [rng.uniform(start, end) for _ in range(count)]


def max_deviation(a, b, angles, predicted, radius=1.0):
    """Largest |angle APB - predicted| for P at the given angles."""
    worst = 0.0
    for t in angles:
        p = point_on_circle(t, radius)
        worst = max(worst, abs(angle_at(a, p, b) - predicted))
    return worst


def main():
    rng = random.Random(2024)
    a, b = point_on_circle(200), point_on_circle(340)
    central = angle_at(a, (0.0, 0.0), b)
    print(f"Chord AB of the unit circle; central angle AOB = {central:.10f} deg")
    print(f"Prediction: {central / 2:.6f} deg on the major arc, "
          f"{180 - central / 2:.6f} deg on the minor arc")
    major = arc_samples(-20 + 0.01, 200 - 0.01, 2000, rng)
    minor = arc_samples(200 + 0.01, 340 - 0.01, 2000, rng)
    print(f"  2000 points P on the major arc: max |APB - {central / 2:.0f}|"
          f" = {max_deviation(a, b, major, central / 2):.1e} deg")
    print(f"  2000 points P on the minor arc: max |APB - "
          f"{180 - central / 2:.0f}| = "
          f"{max_deviation(a, b, minor, 180 - central / 2):.1e} deg")
    d1, d2 = point_on_circle(90), point_on_circle(270)
    thales = arc_samples(-90 + 0.01, 90 - 0.01, 2000, rng)
    print(f"Thales (AB a diameter): max |APB - 90| = "
          f"{max_deviation(d1, d2, thales, 90):.1e} deg")
    print("Off the circle, on the ray from O at 90 deg:")
    for radius in (0.5, 0.9, 1.0, 1.1, 2.0):
        p = point_on_circle(90, radius)
        print(f"  |OP| = {radius:3.1f}: angle APB = {angle_at(a, p, b):8.4f} deg")
    print("Inside the circle the chord looks bigger, outside smaller: on this")
    print("ray only the point on the circle sees AB at exactly 70 deg.")
    print()
    print("Epistemic status: numerical evidence. Each angle is computed in")
    print("floating point, so agreement is up to rounding (about 1e-11 deg),")
    print("and only 6,000 points were tried. The inscribed angle theorem,")
    print("proved in the lesson, covers every point of every circle.")


if __name__ == "__main__":
    main()
