"""Euler's method and RK4: convergence, blow-up and non-uniqueness.

1. For x' = x, x(0) = 1 on [0, 1], Euler's method with n steps gives exactly
   (1 + 1/n)^n, with error about e/(2n): first order. The classical
   fourth-order Runge-Kutta method (RK4) has error about C/n^4.
2. For x' = x^2, x(0) = 1 the solution 1/(1 - t) blows up at t = 1; RK4
   values explode as t approaches 1.
3. For x' = sqrt|x|, x(0) = 0 both x = 0 and x = t^2/4 are solutions. Every
   numerical method started exactly at 0 stays at 0; started at 1e-12 it
   follows the parabola. Numerics cannot detect non-uniqueness.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "ordinary_differential_equations_numerical_methods",
    "title": "Euler and Runge-Kutta: convergence, blow-up, non-uniqueness",
    "evidence": ["numerical", "experimental"],
    "lessons": ["ordinary-differential-equations"],
    "summary": (
        "Solves x' = x with Euler's method and RK4 and measures their orders "
        "(1 and 4); follows RK4 towards the blow-up of x' = x^2 at t = 1; and "
        "shows that for x' = sqrt|x| a method started at 0 stays at 0 while a "
        "start at 1e-12 tracks t^2/4. Floating-point evidence for these "
        "examples; the error theorems and Picard-Lindelof are the proofs."
    ),
    "packages": [],
}


def euler(f, t0, x0, t1, n):
    """Euler's method with n equal steps from (t0, x0) to time t1."""
    h = (t1 - t0) / n
    t, x = t0, x0
    for _ in range(n):
        x = x + h * f(t, x)
        t = t + h
    return x


def rk4(f, t0, x0, t1, n):
    """Classical fourth-order Runge-Kutta method with n equal steps."""
    h = (t1 - t0) / n
    t, x = t0, x0
    for _ in range(n):
        k1 = f(t, x)
        k2 = f(t + h / 2, x + h / 2 * k1)
        k3 = f(t + h / 2, x + h / 2 * k2)
        k4 = f(t + h, x + h * k3)
        x = x + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        t = t + h
    return x


def observed_order(error_n, error_2n):
    """Order p estimated from errors with n and 2n steps (error ~ C h^p)."""
    return math.log2(abs(error_n) / abs(error_2n))


def growth(t, x):
    """Right-hand side of x' = x."""
    return x


def square(t, x):
    """Right-hand side of x' = x^2."""
    return x * x


def sqrt_abs(t, x):
    """Right-hand side of x' = sqrt|x|."""
    return math.sqrt(abs(x))


def main():
    print("1. x' = x, x(0) = 1: error at t = 1 (exact value e)")
    print("     n     Euler error   (1 + 1/n)^n - e     RK4 error")
    prev = None
    for n in [10, 20, 40, 80]:
        e_err = euler(growth, 0.0, 1.0, 1.0, n) - math.e
        formula = (1 + 1 / n) ** n - math.e
        r_err = rk4(growth, 0.0, 1.0, 1.0, n) - math.e
        print(f"   {n:3d}    {e_err:+.3e}      {formula:+.3e}        {r_err:+.3e}")
        if prev:
            p_e = observed_order(prev[0], e_err)
            p_r = observed_order(prev[1], r_err)
        prev = (e_err, r_err)
    print(f"   observed orders (n = 40 -> 80): Euler {p_e:.2f}, RK4 {p_r:.2f}")
    print("2. x' = x^2, x(0) = 1 (solution 1/(1 - t)), RK4 with h = 0.001:")
    for t1 in [0.9, 0.99, 0.999]:
        value = rk4(square, 0.0, 1.0, t1, round(t1 * 1000))
        print(f"   t = {t1:<5}  RK4 {value:12.3f}   exact {1 / (1 - t1):12.3f}")
    print("   with a fixed step RK4 lags behind near the singularity, and past")
    print("   t = 1 there is no solution to approximate.")
    print("3. x' = sqrt|x|: two solutions through (0, 0)")
    for x0 in [0.0, 1e-12]:
        value = rk4(sqrt_abs, 0.0, x0, 2.0, 2000)
        print(f"   start x(0) = {x0:<6g}: RK4 gives x(2) = {value:.6f}")
    print("   (x = 0 and x = t^2/4 both solve the problem; t^2/4 = 1 at t = 2)")
    print()
    print("Epistemic status: floating-point experiments. They agree with the")
    print("theory (Euler is first order, RK4 fourth order for smooth problems;")
    print("1/(1 - t) blows up) but prove nothing; in part 3 the numerics silently")
    print("pick one of two solutions, which only the theory reveals.")


if __name__ == "__main__":
    main()
