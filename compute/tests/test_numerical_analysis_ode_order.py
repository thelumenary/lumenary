import math

import numerical_analysis_ode_order as ex


def observed_order(step, n):
    f = lambda t, y: y
    e1 = abs(ex.integrate(step, f, 1.0, 1.0, n) - math.e)
    e2 = abs(ex.integrate(step, f, 1.0, 1.0, 2 * n) - math.e)
    return math.log2(e1 / e2)


def test_observed_orders():
    assert abs(observed_order(ex.euler_step, 200) - 1) < 0.02
    assert abs(observed_order(ex.heun_step, 100) - 2) < 0.05
    assert abs(observed_order(ex.rk4_step, 20) - 4) < 0.1


def test_methods_exact_on_simple_problems():
    # Euler is exact for y' = 1; Heun is exact for y' = t (quadratic solution).
    assert math.isclose(ex.integrate(ex.euler_step, lambda t, y: 1.0, 0.0, 2.0, 7), 2.0)
    assert math.isclose(ex.integrate(ex.heun_step, lambda t, y: t, 0.0, 1.0, 5), 0.5)
    # RK4 reproduces Simpson's rule: exact for y' = t^3.
    assert math.isclose(ex.integrate(ex.rk4_step, lambda t, y: t ** 3, 0.0, 1.0, 3), 0.25)


def test_stiff_exact_solution_satisfies_ode():
    for t in (0.1, 0.5, 1.0):
        h = 1e-6
        d = (ex.stiff_exact(t + h) - ex.stiff_exact(t - h)) / (2 * h)
        assert abs(d + 50 * (ex.stiff_exact(t) - math.cos(t))) < 1e-5
    assert ex.stiff_exact(0.0) == 0.0


def test_explicit_euler_unstable_backward_stable():
    g = lambda t, y: -50 * (y - math.cos(t))
    bad = abs(ex.integrate(ex.euler_step, g, 0.0, 1.0, 20) - ex.stiff_exact(1.0))
    good = abs(ex.integrate(ex.euler_step, g, 0.0, 1.0, 100) - ex.stiff_exact(1.0))
    back = abs(ex.backward_euler_stiff(-50, 0.0, 1.0, 20) - ex.stiff_exact(1.0))
    assert bad > 100 and good < 1e-3 and back < 1e-3
