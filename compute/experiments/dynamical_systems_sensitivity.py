"""Sensitive dependence, and why a simulation is not the true orbit.

At r = 4 the logistic map is conjugate to the doubling map: if
x = sin^2(pi theta) then 4x(1 - x) = sin^2(2 pi theta). So the true orbit of
x_0 = sin^2(pi theta_0) is x_n = sin^2(2^n pi theta_0), and for rational
theta_0 we can compute 2^n theta_0 mod 1 exactly with fractions. This gives
the true orbit to full floating-point accuracy at every step, which we
compare with naive floating-point iteration of 4x(1 - x). The rounding error
of about 1e-16 doubles at each step, and after about 50 steps the simulated
orbit has nothing to do with the true one. Two true orbits started 1e-10
apart separate the same way. Finally, the doubling map itself in floating
point sends every starting value to 0 within about 55 steps, while in exact
arithmetic the orbit of 1/7 cycles 1/7, 2/7, 4/7 forever.

Evidence: exact rational arithmetic for the true orbits, compared with
floating point; the conjugacy formula is proved in the lesson.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "dynamical_systems_sensitivity",
    "title": "Sensitive dependence: true orbits versus floating point",
    "evidence": ["exact", "numerical", "counterexample"],
    "lessons": ["dynamical-systems"],
    "summary": (
        "Uses the conjugacy x = sin^2(pi theta) between the logistic map at "
        "r = 4 and the doubling map, with exact fractions for theta, to compute "
        "true orbits and compare them with floating-point iteration: the "
        "simulation departs from the true orbit after about 50 steps, nearby "
        "true orbits separate like 2^n, and the float doubling map collapses "
        "to 0 although exact orbits of 1/7 are periodic."
    ),
    "packages": [],
}


def true_orbit(theta0, steps):
    """x_n = sin^2(pi * (2^n theta0 mod 1)) for n = 0..steps (theta0 rational)."""
    theta = Fraction(theta0) % 1
    xs = []
    for _ in range(steps + 1):
        xs.append(math.sin(math.pi * float(theta)) ** 2)
        theta = (2 * theta) % 1
    return xs


def float_orbit(x0, steps, r=4.0):
    """Naive floating-point iteration of x -> r x (1 - x)."""
    xs = [x0]
    for _ in range(steps):
        xs.append(r * xs[-1] * (1 - xs[-1]))
    return xs


def doubling_float(x0, steps):
    """Floating-point doubling map x -> 2x mod 1."""
    xs = [x0]
    for _ in range(steps):
        xs.append((2 * xs[-1]) % 1.0)
    return xs


def doubling_exact(x0, steps):
    """Exact doubling map on fractions."""
    xs = [Fraction(x0)]
    for _ in range(steps):
        xs.append((2 * xs[-1]) % 1)
    return xs


def first_zero(xs):
    """Index of the first exact 0 in a list, or None."""
    for i, x in enumerate(xs):
        if x == 0:
            return i
    return None


def main():
    theta0 = Fraction(1, 7) + Fraction(1, 10 ** 6)
    truth = true_orbit(theta0, 60)
    sim = float_orbit(truth[0], 60)
    near = true_orbit(theta0 + Fraction(1, 10 ** 10), 60)
    print("Logistic map r = 4, x0 = sin^2(pi theta0), theta0 = 1/7 + 1e-6")
    print("   n    true x_n    float x_n   |error|    true orbit from theta0+1e-10")
    for n in range(0, 61, 6):
        err = abs(truth[n] - sim[n])
        print(f"{n:4d}   {truth[n]:.6f}    {sim[n]:.6f}   {err:.1e}"
              f"    {near[n]:.6f}")
    print("Both gaps double at each step: the float error, from about 1e-16,")
    print("reaches order 1 near step 50; the two true orbits, 1e-10 apart in")
    print("theta, separate completely near step 30.")
    print()
    d_float = doubling_float(1 / 7, 80)
    d_exact = doubling_exact(Fraction(1, 7), 80)
    print("Doubling map x -> 2x mod 1 starting at 1/7:")
    print(f"   exact orbit: {', '.join(str(x) for x in d_exact[:7])}, ...")
    print(f"   float orbit reaches exactly 0 at step {first_zero(d_float)}"
          " and stays there")
    print()
    print("Epistemic status: the true orbits are computed from exact fractions")
    print("and the proved conjugacy, so they are correct to float accuracy;")
    print("the float iterations are a counterexample to trusting long")
    print("simulations of chaotic maps. Shadowing theorems explain why such")
    print("simulations can still be close to some other true orbit.")


if __name__ == "__main__":
    main()
