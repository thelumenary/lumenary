"""Light bending and perihelion precession from Schwarzschild geodesics.

With u = 1/r and units G = c = 1, geodesics in the equatorial plane of the
Schwarzschild metric satisfy u'' + u = 3 M u^2 for light and
u'' + u = M / L^2 + 3 M u^2 for planets (' = d/dphi). We integrate both by
the Runge-Kutta method (RK4), locate the end point by bisection, and compare
the light deflection with 4M/b (plus the second-order term 15 pi M^2/(4 b^2))
and the perihelion advance per orbit with 6 pi M/p, p = L^2/M. Finally we
evaluate both leading-order formulas for the Sun and Mercury in SI units.
"""

import math

EXPERIMENT = {
    "id": "relativity_geodesics",
    "title": "Light bending and Mercury's perihelion from geodesics",
    "evidence": ["numerical"],
    "lessons": ["relativity"],
    "summary": (
        "Integrates the Schwarzschild orbit equations u'' + u = 3Mu^2 (light) "
        "and u'' + u = M/L^2 + 3Mu^2 (planets) with RK4 and compares the "
        "deflection angle with 4M/b and the perihelion advance with 6 pi M/p "
        "for several impact parameters and orbits; the ratios tend to 1 as the "
        "field weakens. Then evaluates 1.75 arcseconds for starlight grazing the "
        "Sun and 43 arcseconds per century for Mercury. Floating-point evidence."
    ),
    "packages": [],
}


def rk4_step(f, phi, y, h):
    """One classical Runge-Kutta step for y' = f(phi, y), y = (u, w)."""
    k1 = f(phi, y)
    k2 = f(phi + h / 2, [y[i] + h / 2 * k1[i] for i in range(2)])
    k3 = f(phi + h / 2, [y[i] + h / 2 * k2[i] for i in range(2)])
    k4 = f(phi + h, [y[i] + h * k3[i] for i in range(2)])
    return [y[i] + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i])
            for i in range(2)]


def first_crossing(f, y0, index, sign, h, phi_min):
    """Smallest phi > phi_min where component `index` crosses 0 with the
    given sign of the derivative (+1 upward, -1 downward), by RK4 + bisection.
    """
    phi, y = 0.0, list(y0)
    while True:
        y_next = rk4_step(f, phi, y, h)
        crosses = (y[index] * sign < 0 <= y_next[index] * sign)
        if phi + h > phi_min and crosses:
            lo, hi = 0.0, h
            for _ in range(60):
                mid = (lo + hi) / 2
                if rk4_step(f, phi, y, mid)[index] * sign < 0:
                    lo = mid
                else:
                    hi = mid
            return phi + (lo + hi) / 2
        phi, y = phi + h, y_next


def light_deflection(mass, b, steps=6000):
    """Total deflection angle of a light ray with impact parameter b."""
    def f(_phi, y):
        return [y[1], 3 * mass * y[0] ** 2 - y[0]]
    end = first_crossing(f, [0.0, 1.0 / b], 0, -1, math.pi / steps, 1.0)
    return end - math.pi


def perihelion_advance(mass, p, e, steps=6000):
    """Advance of the perihelion per orbit for an orbit with u_max = (1+e)/p."""
    def f(_phi, y):
        return [y[1], mass / (mass * p) + 3 * mass * y[0] ** 2 - y[0]]
    end = first_crossing(f, [(1 + e) / p, 0.0], 1, -1, 2 * math.pi / steps,
                         math.pi)
    return end - 2 * math.pi


def main():
    print("Light ray past mass M = 1, impact parameter b:")
    print("       b    deflection     4M/b   + 15 pi M^2/(4 b^2)   ratio")
    for b in [10.0, 30.0, 100.0, 1000.0]:
        d = light_deflection(1.0, b)
        lead = 4 / b
        second = lead + 15 * math.pi / (4 * b * b)
        print(f"  {b:>6.0f}   {d:.7f}   {lead:.7f}   {second:.7f}"
              f"          {d / lead:.5f}")
    print()
    print("Bound orbit, eccentricity 0.2, semi-latus rectum p (M = 1):")
    print("       p    advance/orbit   6 pi M/p     ratio")
    for p in [30.0, 100.0, 1000.0, 10000.0]:
        adv = perihelion_advance(1.0, p, 0.2)
        lead = 6 * math.pi / p
        print(f"  {p:>6.0f}   {adv:.8f}      {lead:.8f}   {adv / lead:.5f}")
    print()
    gm, c = 1.32712440018e20, 299792458.0
    r_sun = 6.957e8
    arcsec = 180 / math.pi * 3600
    bend = 4 * gm / (c * c * r_sun) * arcsec
    a, e, period_days = 5.7909050e10, 0.205630, 87.9691
    per_orbit = 6 * math.pi * gm / (c * c * a * (1 - e * e))
    per_century = per_orbit * 36525 / period_days * arcsec
    print(f"Sun: starlight grazing the limb is bent by {bend:.3f} arcsec")
    print(f"Mercury: perihelion advance {per_century:.2f} arcsec per century")
    print()
    print("Epistemic status: RK4 integration in floating point (step errors")
    print("far below the digits shown) of the exact geodesic equations, for")
    print("finitely many cases. The 4M/b and 6 pi M/p laws are leading-order")
    print("theorems derived in the lesson; observations confirm the numbers.")


if __name__ == "__main__":
    main()
