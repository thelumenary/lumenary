"""Kepler's laws from Newton's law, numerically - and why the integrator matters.

We integrate r'' = -r / |r|^3 (units with GM = 1) from r(0) = (1, 0),
v(0) = (0, 1.2). Theory: energy E = -0.28, angular momentum L = 1.2, an
ellipse with eccentricity e = sqrt(1 + 2 E L^2) = 0.44, semi-major axis
a = -1/(2E), perihelion a(1 - e) = 1 and period 2 pi a^(3/2). The velocity
Verlet (leapfrog) method conserves L exactly (up to rounding) and keeps E
within a small bounded band; explicit Euler spirals outwards, gaining energy.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "classical_mechanics_kepler_orbit",
    "title": "Kepler orbits: Verlet versus Euler",
    "evidence": ["numerical"],
    "lessons": ["classical-mechanics"],
    "summary": (
        "Integrates the inverse-square law for an elliptic orbit with the "
        "velocity Verlet method and with explicit Euler, measures energy and "
        "angular momentum drift, the period, perihelion and aphelion, and "
        "compares them with Kepler's laws (e = 0.44, T = 2 pi a^1.5). Numerical "
        "evidence for one orbit; the conservation laws and Kepler's laws are "
        "proved in the lesson."
    ),
    "packages": [],
}


def accel(x, y):
    """Inverse-square attraction towards the origin, GM = 1."""
    r3 = (x * x + y * y) ** 1.5
    return -x / r3, -y / r3


def energy(x, y, vx, vy):
    """Energy per unit mass: kinetic plus potential -1/r."""
    return 0.5 * (vx * vx + vy * vy) - 1 / math.hypot(x, y)


def ang_mom(x, y, vx, vy):
    """Angular momentum per unit mass, x vy - y vx."""
    return x * vy - y * vx


def verlet_step(state, h):
    """One velocity Verlet (leapfrog) step."""
    x, y, vx, vy = state
    ax, ay = accel(x, y)
    vx, vy = vx + h / 2 * ax, vy + h / 2 * ay
    x, y = x + h * vx, y + h * vy
    ax, ay = accel(x, y)
    return x, y, vx + h / 2 * ax, vy + h / 2 * ay


def euler_step(state, h):
    """One explicit Euler step."""
    x, y, vx, vy = state
    ax, ay = accel(x, y)
    return x + h * vx, y + h * vy, vx + h * ax, vy + h * ay


def run(step, state, h, n):
    """Apply n steps; return the list of states (including the initial one)."""
    states = [state]
    for _ in range(n):
        state = step(state, h)
        states.append(state)
    return states


def first_return_time(states, h):
    """Time of the first upward crossing of y = 0 with x > 0 after the start."""
    for i in range(1, len(states)):
        (x0, y0, _, _), (x1, y1, _, _) = states[i - 1], states[i]
        if i > 1 and y0 < 0 <= y1 and x1 > 0:
            return (i - 1 + (-y0) / (y1 - y0)) * h
    return None


def kepler_predictions(state):
    """Energy, angular momentum, eccentricity, semi-major axis and period."""
    E = energy(*state)
    L = ang_mom(*state)
    e = math.sqrt(1 + 2 * E * L * L)
    a = -1 / (2 * E)
    return E, L, e, a, 2 * math.pi * a**1.5


def main():
    start = (1.0, 0.0, 0.0, 1.2)
    E, L, e, a, T = kepler_predictions(start)
    print(f"Theory: E = {E:.4f}, L = {L:.4f}, e = {e:.4f}, a = {a:.4f}")
    print(f"        perihelion {a * (1 - e):.4f}, aphelion {a * (1 + e):.4f},"
          f" period {T:.4f}")
    h, n = 0.001, 60000  # about four orbits
    for name, step in [("Verlet", verlet_step), ("Euler", euler_step)]:
        states = run(step, start, h, n)
        radii = [math.hypot(s[0], s[1]) for s in states]
        energies = [energy(*s) for s in states]
        momenta = [ang_mom(*s) for s in states]
        print(f"{name} (h = {h}, {n} steps):")
        e_drift = max(abs(en - E) for en in energies)
        print(f"   max |E(t) - E(0)| = {e_drift:.2e}")
        drift = max(abs(m - L) for m in momenta)
        print(f"   max |L(t) - L(0)| = {drift:.2e}")
        print(f"   r ranges over [{min(radii):.4f}, {max(radii):.4f}]")
        ret = first_return_time(states, h)
        shown = f"{ret:.4f}" if ret else "none"
        print(f"   first return to the x-axis at t = {shown}")
    print()
    print("Epistemic status: numerical integration of one orbit. Verlet keeps L")
    print("constant to rounding error and E in a narrow band, matching Kepler's")
    print("predictions to several digits; Euler drifts outwards. The laws")
    print("themselves are theorems proved in the lesson, not consequences of")
    print("this simulation.")


if __name__ == "__main__":
    main()
