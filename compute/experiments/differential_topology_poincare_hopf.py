"""Indices of zeros of vector fields, and the Poincare-Hopf theorem.

The index of an isolated zero p of a planar vector field V is the number of
times V turns round as one walks once anticlockwise round a small circle
about p. We compute it by adding up the changes of the angle of V.

Part 1: the basic zeros (source, sink, centre, saddle, z^2, conj(z)^2, z^3).
Part 2: fields on the sphere. Stereographic projection from the north pole
gives a chart z in which z = 0 is the south pole; the chart w = 1/z covers
the north pole, w = 0. A field V(z) becomes W(w) = -w^2 V(1/w) in the second
chart (differentiate w = 1/z along a flow line). The indices always add up to
2 = chi(S^2). Part 3: the gradient of the height function on a torus has a
maximum, a minimum and two saddles, with indices adding up to 0 = chi(T^2).
"""

import cmath
import math

EXPERIMENT = {
    "id": "differential_topology_poincare_hopf",
    "title": "Indices of vector fields and the Poincare-Hopf theorem",
    "evidence": ["numerical"],
    "lessons": ["differential-topology"],
    "summary": (
        "Computes indices of isolated zeros of planar vector fields by summing "
        "angle changes round small circles; checks that the indices of several "
        "fields on the sphere (written in two stereographic charts) add up to 2 "
        "and that the gradient of the height function on a torus has indices "
        "adding up to 0, as the Poincare-Hopf theorem predicts. Numerical."
    ),
    "packages": [],
}


def index(field, centre, radius=1e-3, steps=720):
    """Winding number of the complex-valued field round a small circle."""
    total = 0.0
    previous = cmath.phase(field(centre + radius))
    for k in range(1, steps + 1):
        z = centre + radius * cmath.exp(2j * math.pi * k / steps)
        angle = cmath.phase(field(z))
        step = angle - previous
        step -= 2 * math.pi * round(step / (2 * math.pi))
        total += step
        previous = angle
    return round(total / (2 * math.pi))


def south_chart(field):
    """The same field written in the chart w = 1/z: W(w) = -w^2 V(1/w)."""
    def other(w):
        return -w * w * field(1 / w)
    return other


PLANAR = [
    ("source  V = z", lambda z: z),
    ("sink    V = -z", lambda z: -z),
    ("centre  V = iz", lambda z: 1j * z),
    ("saddle  V = conj(z)", lambda z: z.conjugate()),
    ("dipole  V = z^2", lambda z: z * z),
    ("        V = conj(z)^2", lambda z: z.conjugate() ** 2),
    ("        V = z^3", lambda z: z**3),
]

#: (name, field in the north chart, zeros in the north chart, zero at w = 0?)
SPHERE = [
    ("V = z (flow from S to N)", lambda z: z, [0], True),
    ("V = iz (rotation)", lambda z: 1j * z, [0], True),
    ("V = 1 (constant)", lambda z: 1 + 0j, [], True),
    ("V = z^2 - 1", lambda z: z * z - 1, [1, -1], False),
]


def torus_gradient(big=2.0, small=1.0):
    """Coordinate gradient of h(u, v) = (R + r cos v) cos u, as u + iv."""
    def grad(z):
        u, v = z.real, z.imag
        du = -(big + small * math.cos(v)) * math.sin(u)
        dv = -small * math.sin(v) * math.cos(u)
        return complex(du, dv)
    return grad


def main():
    print("1. Indices of planar zeros at the origin")
    for name, field in PLANAR:
        print(f"   {name:<22} index {index(field, 0):+d}")
    print()
    print("2. Fields on the sphere; W(w) = -w^2 V(1/w) near the north pole")
    for name, field, zeros, at_infinity in SPHERE:
        parts = [index(field, z) for z in zeros]
        if at_infinity:
            parts.append(index(south_chart(field), 0))
        shown = " + ".join(str(p) for p in parts)
        print(f"   {name:<26} {shown} = {sum(parts)}")
    print()
    print("3. Gradient of the height function on a torus (R = 2, r = 1)")
    grad = torus_gradient()
    total = 0
    for name, (u, v) in [("maximum", (0, 0)), ("saddle", (0, math.pi)),
                         ("saddle", (math.pi, math.pi)),
                         ("minimum", (math.pi, 0))]:
        k = index(grad, complex(u, v))
        total += k
        print(f"   {name:<8} at (u, v) = ({u:.2f}, {v:.2f})   index {k:+d}")
    print(f"   sum of indices = {total} = chi(torus)")
    print()
    print("Epistemic status: numerical winding numbers on circles of radius")
    print("0.001, rounded to integers, for a handful of fields. The totals 2 and 0")
    print("are evidence for the Poincare-Hopf theorem, which the lesson states.")


if __name__ == "__main__":
    main()
