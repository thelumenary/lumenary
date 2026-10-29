"""Change of variables: why the Jacobian factor r matters.

We integrate e^(-(x^2 + y^2)) over discs of radius R three ways: on a
Cartesian grid (the honest but slow way), in polar coordinates with the
Jacobian factor r, and in polar coordinates *forgetting* r. The first two
agree with the exact value pi (1 - e^(-R^2)); the third does not. Letting R
grow gives pi, so (integral of e^(-x^2) over the line)^2 = pi - the Gaussian
integral.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import math

EXPERIMENT = {
    "id": "multivariable_calculus_polar_jacobian",
    "title": "Polar coordinates and the Jacobian factor r",
    "evidence": ["numerical"],
    "lessons": ["multivariable-calculus"],
    "summary": (
        "Integrates exp(-(x^2 + y^2)) over discs by a Cartesian midpoint grid, "
        "by polar coordinates with the Jacobian factor r, and by polar "
        "coordinates without it, against the exact value pi (1 - exp(-R^2)). "
        "Forgetting r gives wrong answers. It also checks numerically that the "
        "one-dimensional Gaussian integral is close to sqrt(pi)."
    ),
    "packages": [],
}


def gauss2(x, y):
    """The two-dimensional Gaussian exp(-(x^2 + y^2))."""
    return math.exp(-(x * x + y * y))


def cartesian_disc(f, radius, n=400):
    """Midpoint rule on an n x n grid over [-R, R]^2, keeping cells in the disc."""
    h = 2 * radius / n
    total = 0.0
    for i in range(n):
        x = -radius + (i + 0.5) * h
        for j in range(n):
            y = -radius + (j + 0.5) * h
            if x * x + y * y <= radius * radius:
                total += f(x, y)
    return total * h * h


def polar_disc(f, radius, n_r=400, n_t=64, jacobian=True):
    """Midpoint rule in (r, theta); include the factor r unless jacobian=False."""
    hr, ht = radius / n_r, 2 * math.pi / n_t
    total = 0.0
    for i in range(n_r):
        r = (i + 0.5) * hr
        weight = r if jacobian else 1.0
        for j in range(n_t):
            t = (j + 0.5) * ht
            total += f(r * math.cos(t), r * math.sin(t)) * weight
    return total * hr * ht


def exact_disc(radius):
    """Exact integral of exp(-(x^2 + y^2)) over the disc: pi (1 - e^(-R^2))."""
    return math.pi * (1 - math.exp(-radius * radius))


def gaussian_line(limit=8.0, n=4000):
    """Midpoint-rule approximation of the integral of e^(-x^2) over [-L, L]."""
    h = 2 * limit / n
    return h * sum(math.exp(-((-limit + (i + 0.5) * h) ** 2)) for i in range(n))


def main():
    print("Integral of exp(-(x^2 + y^2)) over the disc of radius R")
    print("  R    exact      Cartesian   polar with r   polar without r")
    for radius in [0.5, 1.0, 2.0, 3.0]:
        exact = exact_disc(radius)
        cart = cartesian_disc(gauss2, radius, n=200)
        good = polar_disc(gauss2, radius)
        bad = polar_disc(gauss2, radius, jacobian=False)
        print(f"  {radius:<4} {exact:.6f}   {cart:.6f}    {good:.6f}       {bad:.6f}")
    print("The Cartesian grid has a jagged edge along the circle, which limits")
    print("its accuracy; polar coordinates with r match the exact value.")
    print("Without r the 'area element' dr dtheta is wrong: it overweights the")
    print("centre, where small r squeezes the polar rectangles together.")
    print()
    big = exact_disc(6.0)
    line = gaussian_line()
    print(f"As R grows the disc integral tends to pi: R = 6 gives {big:.12f}")
    print(f"Integral of e^(-x^2) over [-8, 8] (midpoint rule) = {line:.12f}")
    print(f"sqrt(pi)                                       = {math.sqrt(math.pi):.12f}")
    print()
    print("Epistemic status: numerical quadrature for a few radii - evidence that")
    print("dx dy = r dr dtheta, not a proof. The change of variables theorem and")
    print("the exact Gaussian integral sqrt(pi) are proved in the lesson (and in")
    print("Mathlib, cited in the lesson's Lean file).")


if __name__ == "__main__":
    main()
