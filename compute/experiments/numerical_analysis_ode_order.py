"""Order, stiffness and rounding: one-step methods for ODEs.

(1) Observed order: solve y' = y, y(0) = 1 on [0, 1] with Euler, Heun
(a second-order Runge-Kutta method) and classical RK4, halving the step
each time. If the global error is C h^p, halving h divides it by 2^p, so
log2 of successive error ratios estimates the order p: we see 1, 2 and 4.
(2) Stiffness: y' = -50 (y - cos t), y(0) = 0 has a smooth solution, but
explicit Euler is stable only for h * 50 < 2. With h = 0.05 it explodes;
backward Euler is stable for every h. (3) Rounding: the difference
quotient (e^(1+h) - e)/h approximates e with truncation error ~ h e/2 and
rounding error ~ u e/h, so the total error is smallest near h = sqrt(u)
and grows again for smaller h.

Evidence: numerical, compared with exact solutions.
"""

import math

EXPERIMENT = {
    "id": "numerical_analysis_ode_order",
    "title": "One-step ODE methods: order, stiffness and rounding",
    "evidence": ["numerical"],
    "lessons": ["numerical-analysis"],
    "summary": (
        "Measures the observed order of Euler (1), Heun (2) and classical RK4 "
        "(4) on y' = y; shows explicit Euler exploding on the stiff equation "
        "y' = -50 (y - cos t) when h > 2/50 while backward Euler stays "
        "accurate; and shows the total error of a difference quotient "
        "falling and then rising as h shrinks, because of rounding."
    ),
    "packages": [],
}


def euler_step(f, t, y, h):
    """Explicit Euler."""
    return y + h * f(t, y)


def heun_step(f, t, y, h):
    """Heun's method (explicit trapezoid rule), order 2."""
    k1 = f(t, y)
    k2 = f(t + h, y + h * k1)
    return y + h * (k1 + k2) / 2


def rk4_step(f, t, y, h):
    """Classical fourth-order Runge-Kutta method."""
    k1 = f(t, y)
    k2 = f(t + h / 2, y + h * k1 / 2)
    k3 = f(t + h / 2, y + h * k2 / 2)
    k4 = f(t + h, y + h * k3)
    return y + h * (k1 + 2 * k2 + 2 * k3 + k4) / 6


def integrate(step, f, y0, t_end, n):
    """Take n equal steps of a one-step method from t = 0."""
    h = t_end / n
    t, y = 0.0, y0
    for _ in range(n):
        y = step(f, t, y, h)
        t += h
    return y


def backward_euler_stiff(lam, y0, t_end, n):
    """Backward Euler for y' = lam (y - cos t): solve the linear step exactly."""
    h = t_end / n
    t, y = 0.0, y0
    for _ in range(n):
        t += h
        y = (y - h * lam * math.cos(t)) / (1 - h * lam)
    return y


def stiff_exact(t):
    """Exact solution of y' = -50 (y - cos t), y(0) = 0."""
    a, b = 2500 / 2501, 50 / 2501
    return a * math.cos(t) + b * math.sin(t) - a * math.exp(-50 * t)


def main():
    f = lambda t, y: y
    print("1. y' = y on [0, 1]: error at t = 1 and observed order")
    print("     n      Euler   order       Heun   order        RK4   order")
    prev = None
    for n in [10, 20, 40, 80]:
        errs = [abs(integrate(s, f, 1.0, 1.0, n) - math.e)
                for s in (euler_step, heun_step, rk4_step)]
        cells = []
        for k, e in enumerate(errs):
            order = "" if prev is None else f"{math.log2(prev[k] / e):.2f}"
            cells.append(f"{e:9.2e}  {order:>5}")
        print((f"  {n:4d}   " + "   ".join(cells)).rstrip())
        prev = errs
    print()
    g = lambda t, y: -50 * (y - math.cos(t))
    print("2. Stiff: y' = -50 (y - cos t), y(0) = 0; error at t = 1")
    for n in [20, 25, 40, 100]:
        e1 = abs(integrate(euler_step, g, 0.0, 1.0, n) - stiff_exact(1.0))
        e2 = abs(backward_euler_stiff(-50, 0.0, 1.0, n) - stiff_exact(1.0))
        print(f"   h = {1 / n:5.3f} (50h = {50 / n:4.2f}): explicit {e1:9.2e},"
              f"  backward {e2:8.2e}")
    print()
    print("3. Forward difference for (e^x)' at x = 1: total error")
    for k in [2, 4, 6, 8, 10, 12, 14]:
        h = 10.0 ** -k
        err = abs((math.exp(1 + h) - math.e) / h - math.e)
        print(f"   h = 1e-{k:02d}: error {err:.1e}")
    print()
    print("Epistemic status: numerical experiments. The orders 1, 2, 4, the")
    print("stability limit 50h < 2 and the optimal h near sqrt(u) are")
    print("theorems or estimates proved in the lesson; these runs illustrate")
    print("them on single examples and prove nothing in general.")


if __name__ == "__main__":
    main()
