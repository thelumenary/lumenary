"""Curve-shortening flow: a wiggly curve becomes round and vanishes.

Under curve-shortening flow each point of a closed plane curve moves with
velocity kappa N (curvature times the inward normal). Two exact facts:

* the enclosed area decreases at the constant rate 2 pi, because
  dA/dt = -(integral of kappa ds) = -2 pi for an embedded curve, so the curve
  vanishes at time T = A(0) / (2 pi);
* (Gage-Hamilton 1986, Grayson 1987) an embedded curve becomes convex, then
  asymptotically round: L^2 / (4 pi A) -> 1.

We approximate the flow on the non-convex curve r = 1 + 0.3 cos(3 theta) by a
polygon with 120 vertices, moving each vertex by the discrete curvature vector
(the change of unit tangent per unit length) with small explicit time steps,
and redistributing the vertices evenly along the curve after each step.
"""

import math

import numpy as np

EXPERIMENT = {
    "id": "geometric_analysis_curve_shortening",
    "title": "Curve-shortening flow: area falls at rate 2 pi, shapes round off",
    "evidence": ["numerical"],
    "lessons": ["geometric-analysis"],
    "summary": (
        "Discretises curve-shortening flow for a non-convex three-lobed curve with "
        "a 120-vertex polygon and explicit time steps. Compares the area with the "
        "exact law A(t) = A(0) - 2 pi t, tracks the isoperimetric ratio "
        "L^2/(4 pi A) towards 1 and the moment the curve becomes convex, as the "
        "Gage-Hamilton-Grayson theorem predicts. Numerical approximation with "
        "discretisation error."
    ),
    "packages": ["numpy"],
}

N = 120


def initial_curve(n=N):
    """Vertices of r = 1 + 0.3 cos(3 theta) as an (n, 2) array."""
    t = np.linspace(0.0, 2 * math.pi, n, endpoint=False)
    r = 1 + 0.3 * np.cos(3 * t)
    return np.stack([r * np.cos(t), r * np.sin(t)], axis=1)


def area(p):
    """Signed area of a closed polygon (shoelace formula)."""
    x, y = p[:, 0], p[:, 1]
    return 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))


def length(p):
    """Perimeter of a closed polygon."""
    return float(np.sum(np.linalg.norm(np.roll(p, -1, axis=0) - p, axis=1)))


def curvature_vectors(p):
    """Discrete curvature vector at each vertex: dT/ds."""
    e = np.roll(p, -1, axis=0) - p
    lens = np.linalg.norm(e, axis=1)
    tang = e / lens[:, None]
    dt = tang - np.roll(tang, 1, axis=0)
    ds = 0.5 * (lens + np.roll(lens, 1))
    return dt / ds[:, None]


def turning_angles(p):
    """Signed exterior angles at the vertices (they sum to 2 pi)."""
    e = np.roll(p, -1, axis=0) - p
    ang = np.arctan2(e[:, 1], e[:, 0])
    d = ang - np.roll(ang, 1)
    return (d + math.pi) % (2 * math.pi) - math.pi


def redistribute(p):
    """Place the vertices at equal arc-length spacing along the polygon."""
    closed = np.vstack([p, p[:1]])
    seg = np.linalg.norm(np.diff(closed, axis=0), axis=1)
    s = np.concatenate([[0.0], np.cumsum(seg)])
    target = np.linspace(0.0, s[-1], len(p), endpoint=False)
    return np.stack([np.interp(target, s, closed[:, 0]),
                     np.interp(target, s, closed[:, 1])], axis=1)


def flow(p, t_end, cfl=0.2):
    """Run the discrete flow until time t_end; return the final polygon."""
    t = 0.0
    while t < t_end - 1e-12:
        h = length(p) / len(p)
        dt = min(cfl * h * h, t_end - t)
        p = redistribute(p + dt * curvature_vectors(p))
        t += dt
    return p


def main():
    p = initial_curve()
    a0 = area(p)
    print(f"Initial curve r = 1 + 0.3 cos 3theta: area {a0:.4f}")
    print(f"Smallest turning angle {turning_angles(p).min():+.4f} < 0: not convex")
    print(f"Exact law A(t) = A(0) - 2 pi t; extinction at T = "
          f"{a0 / (2 * math.pi):.4f}")
    print("    t     area   A(0)-2pi t  L^2/(4 pi A)  convex?")
    t = 0.0
    for t_next in (0.0, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.45):
        p = flow(p, t_next - t)
        t = t_next
        a, ratio = area(p), length(p) ** 2 / (4 * math.pi * area(p))
        convex = "yes" if turning_angles(p).min() > 0 else "no"
        print(f"{t:6.3f}  {a:7.4f}  {a0 - 2 * math.pi * t:10.4f}"
              f"  {ratio:12.5f}  {convex}")
    print(f"Sum of turning angles (any polygon): {turning_angles(p).sum():.6f}"
          f" = 2 pi")
    print()
    print("Epistemic status: numerical approximation of a PDE. The polygon,")
    print("explicit time steps and redistribution introduce discretisation")
    print("errors (visible as small gaps between the area columns). The exact")
    print("law dA/dt = -2 pi and the Gage-Hamilton-Grayson theorem are proved")
    print("theorems; this run illustrates them for one curve and proves nothing.")


if __name__ == "__main__":
    main()
