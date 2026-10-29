"""The period of a pendulum: small-angle law, exact formula and simulation.

For theta'' = -(g/l) sin theta released from rest at amplitude theta0,
conservation of energy gives the exact period
    T = 4 sqrt(l/g) K(k),  k = sin(theta0 / 2),
where K is the complete elliptic integral of the first kind. Gauss's
arithmetic-geometric mean computes it: K(k) = pi / (2 AGM(1, sqrt(1 - k^2))).
We compare this with the small-angle period 2 pi sqrt(l/g), with the series
T0 (1 + theta0^2/16 + 11 theta0^4/3072), and with a numerical simulation.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "classical_mechanics_pendulum_period",
    "title": "Pendulum period: small angles, elliptic integrals, simulation",
    "evidence": ["numerical", "exact"],
    "lessons": ["classical-mechanics"],
    "summary": (
        "Computes the exact period of a pendulum for several amplitudes with "
        "Gauss's arithmetic-geometric mean (elliptic integral), compares it with "
        "the small-angle period, a two-term series correction and a velocity "
        "Verlet simulation. Shows that the period grows with amplitude and "
        "diverges as the amplitude approaches 180 degrees."
    ),
    "packages": [],
}


def agm(a, b, tol=1e-15):
    """Arithmetic-geometric mean of positive a and b."""
    if a <= 0 or b <= 0:
        raise ValueError("AGM needs positive numbers")
    while abs(a - b) > tol * a:
        a, b = (a + b) / 2, math.sqrt(a * b)
    return a


def exact_period(theta0, omega0=1.0):
    """Exact period 2 pi / (omega0 AGM(1, cos(theta0/2))), for 0 <= theta0 < pi."""
    if not 0 <= theta0 < math.pi:
        raise ValueError("amplitude must lie in [0, pi)")
    return 2 * math.pi / (omega0 * agm(1.0, math.cos(theta0 / 2)))


def series_period(theta0, omega0=1.0):
    """Two-term series T0 (1 + theta0^2/16 + 11 theta0^4/3072)."""
    t0 = 2 * math.pi / omega0
    return t0 * (1 + theta0**2 / 16 + 11 * theta0**4 / 3072)


def simulated_period(theta0, h=1e-3):
    """Period from velocity Verlet: four times the time to first reach theta = 0."""
    theta, omega, t = theta0, 0.0, 0.0
    while True:
        a = -math.sin(theta)
        omega_half = omega + h / 2 * a
        new_theta = theta + h * omega_half
        omega = omega_half + h / 2 * (-math.sin(new_theta))
        if new_theta <= 0 < theta:
            frac = theta / (theta - new_theta)
            return 4 * (t + frac * h)
        theta, t = new_theta, t + h


def main():
    print("Pendulum with g/l = 1 (small-angle period 2 pi = 6.283185)")
    print("amplitude   exact (AGM)   series      simulated    exact / 2pi")
    for degrees in [5, 30, 60, 90, 120, 150, 170]:
        theta0 = math.radians(degrees)
        ex = exact_period(theta0)
        se = series_period(theta0)
        si = simulated_period(theta0)
        ratio = ex / (2 * math.pi)
        print(f"  {degrees:3d} deg    {ex:9.6f}   {se:9.6f}   {si:9.6f}"
              f"    {ratio:8.4f}")
    print("Small swings are almost isochronous (Galileo's observation), but a")
    print("swing of 90 degrees takes 18% longer, and the period grows without")
    print("bound as the amplitude approaches 180 degrees (the inverted pendulum")
    print("is an unstable equilibrium).")
    print()
    print("Epistemic status: the exact column evaluates a proved formula")
    print("(energy conservation plus Gauss's AGM identity for elliptic")
    print("integrals) in floating point; the simulated column is numerical")
    print("evidence that agrees with it to about six digits.")


if __name__ == "__main__":
    main()
