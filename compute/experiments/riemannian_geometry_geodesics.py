"""Geodesics, the spreading of nearby geodesics, and Clairaut's relation.

Part 1 integrates the geodesic equations (with their Christoffel symbols) on
the unit sphere and on the hyperbolic upper half-plane, for two geodesics
leaving the same point at a small angle delta. The distance between them
after time t, divided by delta, is compared with the Jacobi-field prediction
sin t (curvature +1), t (curvature 0) and sinh t (curvature -1). On the sphere
the geodesics meet again at t = pi: the conjugate point.

Part 2 integrates a geodesic on a torus of revolution and checks Clairaut's
relation: rho^2 du/dt (rho = distance from the axis) stays constant, and the
geodesic never enters the region where rho is smaller than that constant.
Runge-Kutta integration: numerical evidence.
"""

import math

EXPERIMENT = {
    "id": "riemannian_geometry_geodesics",
    "title": "Geodesic spreading, conjugate points and Clairaut's relation",
    "evidence": ["numerical"],
    "lessons": ["riemannian-geometry"],
    "summary": (
        "Integrates geodesic equations by Runge-Kutta on the unit sphere and the "
        "hyperbolic half-plane and measures how fast two geodesics from one point "
        "separate: the ratio distance/angle follows sin t and sinh t, the Jacobi "
        "fields of curvature +1 and -1, with refocusing at t = pi on the sphere. "
        "Then checks Clairaut's conserved quantity along a geodesic on a torus."
    ),
    "packages": [],
}


def rk4(rhs, state, dt, steps):
    """Integrate state' = rhs(state) with the classical Runge-Kutta method."""
    for _ in range(steps):
        k1 = rhs(state)
        k2 = rhs([s + dt / 2 * k for s, k in zip(state, k1)])
        k3 = rhs([s + dt / 2 * k for s, k in zip(state, k2)])
        k4 = rhs([s + dt * k for s, k in zip(state, k3)])
        state = [s + dt / 6 * (a + 2 * b + 2 * c + d)
                 for s, a, b, c, d in zip(state, k1, k2, k3, k4)]
    return state


def sphere_rhs(s):
    """Geodesic equations on the sphere in (theta, phi): state (th, ph, th', ph')."""
    th, ph, dth, dph = s
    return [dth, dph, math.sin(th) * math.cos(th) * dph**2,
            -2 * math.cos(th) / math.sin(th) * dth * dph]


def half_plane_rhs(s):
    """Geodesic equations of (dx^2 + dy^2)/y^2: x'' = 2x'y'/y, y'' = (y'^2 - x'^2)/y."""
    x, y, dx, dy = s
    return [dx, dy, 2 * dx * dy / y, (dy**2 - dx**2) / y]


def sphere_distance(a, b):
    """Great-circle distance between points given in (theta, phi)."""
    def xyz(p):
        return (math.sin(p[0]) * math.cos(p[1]), math.sin(p[0]) * math.sin(p[1]),
                math.cos(p[0]))
    dot = sum(u * v for u, v in zip(xyz(a), xyz(b)))
    cross = math.sqrt(max(0.0, 1 - dot * dot))
    return math.atan2(cross, dot)


def half_plane_distance(a, b):
    """Hyperbolic distance: cosh d = 1 + |a - b|^2 / (2 y_a y_b)."""
    sq = (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2
    return math.acosh(1 + sq / (2 * a[1] * b[1]))


def spread(model, t, delta=1e-4, dt=1e-3):
    """Distance at time t between unit-speed geodesics at angle delta, / delta."""
    steps = max(1, round(t / dt))
    step = t / steps
    # Both start points have an orthonormal coordinate frame: the equator of
    # the sphere (theta = pi/2) and the point (0, 1) of the half-plane.
    if model == "sphere":
        rhs, dist, start = sphere_rhs, sphere_distance, (math.pi / 2, 0.0)
    else:
        rhs, dist, start = half_plane_rhs, half_plane_distance, (0.0, 1.0)
    ends = []
    for angle in (0.3, 0.3 + delta):
        state = [start[0], start[1], math.cos(angle), math.sin(angle)]
        ends.append(rk4(rhs, state, step, steps)[:2])
    return dist(ends[0], ends[1]) / delta


def torus_rhs(big, small):
    """Geodesic equations on the torus metric (R + r cos v)^2 du^2 + r^2 dv^2."""
    def rhs(s):
        u, v, du, dv = s
        rho = big + small * math.cos(v)
        drho = -small * math.sin(v)
        return [du, dv, -2 * drho / rho * du * dv, rho * drho / small**2 * du**2]
    return rhs


def clairaut_run(big=2.0, small=1.0, angle=1.2, t=30.0, dt=1e-3):
    """Return (initial rho^2 u', max deviation, min rho visited) along a geodesic."""
    rho0 = big + small
    state = [0.0, 0.0, math.cos(angle) / rho0, math.sin(angle) / small]
    rhs = torus_rhs(big, small)
    c0 = rho0**2 * state[2]
    worst, min_rho = 0.0, rho0
    for _ in range(round(t / 0.5)):
        state = rk4(rhs, state, dt, round(0.5 / dt))
        rho = big + small * math.cos(state[1])
        worst = max(worst, abs(rho**2 * state[2] - c0))
        min_rho = min(min_rho, rho)
    return c0, worst, min_rho


def main():
    print("1. Two geodesics from one point at angle delta = 1e-4:")
    print("   t      sphere d/delta   sin t      half-plane d/delta   sinh t")
    for t in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, math.pi]:
        a, b = spread("sphere", t), spread("half-plane", t)
        print(f"   {t:4.2f}   {a:12.6f}   {math.sin(t):9.6f}   "
              f"{b:14.6f}       {math.sinh(t):9.6f}")
    print("   Flat plane: d/delta = t exactly. At t = pi the sphere's geodesics")
    print("   meet again at the antipode (a conjugate point).")
    print()
    c0, worst, min_rho = clairaut_run()
    print("2. A geodesic on the torus (R = 2, r = 1) for time 30:")
    print(f"   Clairaut constant rho^2 u' = {c0:.10f}")
    print(f"   largest deviation along the geodesic: {worst:.1e}")
    print(f"   smallest rho visited: {min_rho:.4f} >= |constant| = {abs(c0):.4f}")
    print()
    print("Epistemic status: numerical integration (Runge-Kutta, step 0.001) of")
    print("the geodesic equations. The agreement with sin t and sinh t is evidence")
    print("for the Jacobi equation J'' + K J = 0; the conservation in part 2 is")
    print("evidence for Clairaut's theorem, which the lesson proves.")


if __name__ == "__main__":
    main()
