"""Symplectic and non-symplectic integrators for the pendulum.

Hamilton's equations for the pendulum H(q, p) = p^2/2 - cos q are solved
numerically by four one-step methods. Explicit Euler and the classical
Runge-Kutta method (RK4) are not symplectic; symplectic Euler and the
Stormer-Verlet (leapfrog) method are. We record the energy error over a long
run, and for the harmonic oscillator H = (q^2 + p^2)/2 we compute, with exact
fractions, the determinant of one step of each method: the factor by which
the step multiplies phase-space area.

Evidence: numerical (floating-point runs of finitely many steps) and exact
(rational determinants for one step size). Neither replaces the theorems
(Liouville's theorem; backward error analysis for symplectic methods).
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "symplectic_geometry_integrators",
    "title": "Symplectic integrators: energy drift and phase-space area",
    "evidence": ["numerical", "exact"],
    "lessons": ["symplectic-geometry"],
    "summary": (
        "Integrates the pendulum with explicit Euler, symplectic Euler, "
        "leapfrog and RK4 for 40,000 steps and reports the energy error, then "
        "computes exactly (with fractions) how much one step of each method "
        "scales phase-space area for the harmonic oscillator. Numerical runs "
        "illustrate, but do not prove, the long-time behaviour of the methods."
    ),
    "packages": [],
}


def energy(q, p):
    """The pendulum Hamiltonian H(q, p) = p^2/2 - cos q."""
    return p * p / 2 - math.cos(q)


def force(q):
    """-dH/dq for the pendulum."""
    return -math.sin(q)


def explicit_euler(q, p, h):
    """One explicit Euler step (not symplectic)."""
    return q + h * p, p + h * force(q)


def symplectic_euler(q, p, h):
    """Kick then drift: p <- p + h F(q), q <- q + h p (symplectic)."""
    p = p + h * force(q)
    return q + h * p, p


def leapfrog(q, p, h):
    """Stormer-Verlet: half kick, drift, half kick (symplectic, order 2)."""
    p = p + h / 2 * force(q)
    q = q + h * p
    return q, p + h / 2 * force(q)


def rk4(q, p, h):
    """Classical fourth-order Runge-Kutta step (not symplectic)."""
    def f(a, b):
        return b, force(a)
    k1 = f(q, p)
    k2 = f(q + h / 2 * k1[0], p + h / 2 * k1[1])
    k3 = f(q + h / 2 * k2[0], p + h / 2 * k2[1])
    k4 = f(q + h * k3[0], p + h * k3[1])
    q = q + h / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
    p = p + h / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
    return q, p


METHODS = [
    ("explicit Euler", explicit_euler),
    ("symplectic Euler", symplectic_euler),
    ("leapfrog", leapfrog),
    ("RK4", rk4),
]


def energy_errors(step, q, p, h, n, checkpoints):
    """Run n steps; return {k: max |H - H0| over the first k steps}."""
    e0 = energy(q, p)
    out, worst = {}, 0.0
    for k in range(1, n + 1):
        q, p = step(q, p, h)
        worst = max(worst, abs(energy(q, p) - e0))
        if k in checkpoints:
            out[k] = worst
    return out


def oscillator_step_matrix(name, h):
    """Exact 2x2 matrix of one step for H = (q^2 + p^2)/2, entries Fractions."""
    h = Fraction(h)
    if name == "explicit Euler":
        return [[1, h], [-h, 1]]
    if name == "symplectic Euler":
        return [[1 - h * h, h], [-h, 1]]
    if name == "leapfrog":
        return [[1 - h * h / 2, h], [-h + h ** 3 / 4, 1 - h * h / 2]]
    if name == "RK4":
        a = 1 - h ** 2 / 2 + h ** 4 / 24
        b = h - h ** 3 / 6
        return [[a, b], [-b, a]]
    raise ValueError(name)


def det2(m):
    """Determinant of a 2x2 matrix."""
    return m[0][0] * m[1][1] - m[0][1] * m[1][0]


def main():
    h, n, checks = 0.2, 40000, (100, 1000, 10000, 40000)
    print("Pendulum H = p^2/2 - cos q, start (q, p) = (2, 0), step h = 0.2")
    print("Largest energy error max|H - H0| up to time t:")
    print(f"{'method':<18}" + "".join(f"{f't = {k * h:g}':>15}"
                                      for k in checks))
    for name, step in METHODS:
        errs = energy_errors(step, 2.0, 0.0, h, n, set(checks))
        print(f"{name:<18}" + "".join(f"{errs[k]:>15.2e}" for k in checks))
    print()
    print("One step for H = (q^2 + p^2)/2 with h = 1/10: exact det of the map")
    for name, _ in METHODS:
        d = det2(oscillator_step_matrix(name, Fraction(1, 10)))
        print(f"  {name:<18} det = {str(d):<26} ~ {float(d):.12f}")
    grow = float(Fraction(101, 100) ** 1000)
    print(f"Explicit Euler multiplies area by (1.01)^1000 ~ {grow:.3g} "
          "in 1000 steps.")
    print()
    print("Epistemic status: the energy table is numerical evidence from")
    print("floating-point runs of finitely many steps; it shows bounded energy")
    print("error for the two symplectic methods and growth (fast for explicit")
    print("Euler, slow for RK4) for the others, but proves nothing about all")
    print("times. The determinants are exact: the symplectic steps preserve")
    print("area exactly, while Euler expands it and RK4 contracts it slightly.")


if __name__ == "__main__":
    main()
