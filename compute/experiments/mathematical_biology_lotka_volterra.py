"""Lotka-Volterra cycles: what a conserved quantity says about numerical methods.

Prey x and predators y obey x' = a x - b x y, y' = d x y - c y. The quantity
V = d x - c ln x + b y - a ln y is exactly conserved, so true orbits are closed.
We integrate with Euler's method and with classical Runge-Kutta (RK4) and
watch V: Euler's orbit spirals outward (V grows steadily), while RK4 keeps V
constant to many digits. With RK4 we also measure the period and check that
the average prey population over one cycle equals the equilibrium value c/d.
"""

import math

EXPERIMENT = {
    "id": "mathematical_biology_lotka_volterra",
    "title": "Lotka-Volterra: conserved quantity, Euler versus RK4, cycle averages",
    "evidence": ["numerical"],
    "lessons": ["mathematical-biology"],
    "summary": (
        "Integrates the Lotka-Volterra predator-prey equations with Euler's method and "
        "with RK4 and monitors the conserved quantity V: Euler drifts outward, RK4 "
        "conserves V closely. Measures the period of the cycle and the average prey and "
        "predator populations over one period, which match the equilibrium (c/d, a/b). "
        "Floating-point numerical evidence."
    ),
    "packages": [],
}

A, B, C, D = 1.0, 0.5, 0.75, 0.25  # prey growth, predation, predator death, conversion


def rhs(x, y):
    """Lotka-Volterra vector field."""
    return A * x - B * x * y, D * x * y - C * y


def conserved(x, y):
    """V = d x - c ln x + b y - a ln y."""
    return D * x - C * math.log(x) + B * y - A * math.log(y)


def euler_step(x, y, h):
    """One explicit Euler step."""
    fx, fy = rhs(x, y)
    return x + h * fx, y + h * fy


def rk4_step(x, y, h):
    """One classical Runge-Kutta step."""
    k1 = rhs(x, y)
    k2 = rhs(x + h / 2 * k1[0], y + h / 2 * k1[1])
    k3 = rhs(x + h / 2 * k2[0], y + h / 2 * k2[1])
    k4 = rhs(x + h * k3[0], y + h * k3[1])
    return (x + h / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]),
            y + h / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]))


def run(step, x, y, h, n):
    """Positions after 0, 1, ..., n steps."""
    path = [(x, y)]
    for _ in range(n):
        x, y = step(x, y, h)
        path.append((x, y))
    return path


def period_and_averages(x0, y0, h=0.001, t_max=40.0):
    """Period (time between successive upward crossings of y = a/b by the
    prey-rich branch) and the averages of x and y over that period, with RK4."""
    x, y = x0, y0
    crossings, t = [], 0.0
    sums, sx, sy = [], 0.0, 0.0
    while t < t_max and len(crossings) < 3:
        nx, ny = rk4_step(x, y, h)
        sx += h * (x + nx) / 2
        sy += h * (y + ny) / 2
        if y < A / B <= ny and nx > C / D:
            crossings.append(t + h)
            sums.append((sx, sy))
        x, y, t = nx, ny, t + h
    period = crossings[2] - crossings[1]
    avg_x = (sums[2][0] - sums[1][0]) / period
    avg_y = (sums[2][1] - sums[1][1]) / period
    return period, avg_x, avg_y


def main():
    x0, y0, h, n = 4.0, 1.0, 0.01, 3000
    v0 = conserved(x0, y0)
    eul = run(euler_step, x0, y0, h, n)
    rk = run(rk4_step, x0, y0, h, n)
    print(f"a = {A}, b = {B}, c = {C}, d = {D}; equilibrium (c/d, a/b) ="
          f" ({C / D:g}, {A / B:g})")
    print(f"Start (x, y) = ({x0}, {y0}), V = {v0:.6f}; step h = {h}")
    print("    t     V (Euler)      V (RK4)     max prey (Euler, RK4)")
    for k in [0, 500, 1000, 2000, 3000]:
        me = max(p[0] for p in eul[:k + 1])
        mr = max(p[0] for p in rk[:k + 1])
        print(f"{k * h:>5.0f} {conserved(*eul[k]):>12.6f} {conserved(*rk[k]):>12.6f}"
              f"   {me:>8.3f} {mr:>8.3f}")
    print("Euler's orbit spirals outward; RK4 stays on the closed level curve.")
    print()
    period, ax, ay = period_and_averages(x0, y0)
    print(f"RK4 period of the cycle: {period:.3f}"
          f" (small-oscillation value 2 pi/sqrt(ac) = {2 * math.pi / math.sqrt(A * C):.3f})")
    print(f"Average prey over a cycle {ax:.4f} (equilibrium c/d = {C / D:.4f})")
    print(f"Average predators         {ay:.4f} (equilibrium a/b = {A / B:.4f})")
    print()
    print("Epistemic status: floating-point integration with fixed steps. The")
    print("conservation of V and the cycle averages are theorems (V and the")
    print("prey average are proved in Lean); the numbers show how well each")
    print("method respects them.")


if __name__ == "__main__":
    main()
