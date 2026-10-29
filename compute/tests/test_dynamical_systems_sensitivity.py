import math
from fractions import Fraction

import dynamical_systems_sensitivity as ex


def test_conjugacy_true_orbit_satisfies_the_map():
    xs = ex.true_orbit(Fraction(3, 11) + Fraction(1, 1000), 30)
    for a, b in zip(xs, xs[1:]):
        assert abs(4 * a * (1 - a) - b) < 1e-9


def test_periodic_true_orbit():
    xs = ex.true_orbit(Fraction(1, 7), 9)
    assert math.isclose(xs[0], xs[3]) and math.isclose(xs[3], xs[6])
    assert not math.isclose(xs[0], xs[1])


def test_float_orbit_agrees_early_and_fails_late():
    theta0 = Fraction(1, 7) + Fraction(1, 10 ** 6)
    truth = ex.true_orbit(theta0, 60)
    sim = ex.float_orbit(truth[0], 60)
    assert abs(truth[10] - sim[10]) < 1e-10
    assert max(abs(a - b) for a, b in zip(truth[50:], sim[50:])) > 0.01


def test_doubling_map_exact_versus_float():
    exact = ex.doubling_exact(Fraction(1, 7), 9)
    assert exact[:4] == [Fraction(1, 7), Fraction(2, 7), Fraction(4, 7), Fraction(1, 7)]
    flt = ex.doubling_float(1 / 7, 80)
    z = ex.first_zero(flt)
    assert z is not None and 50 <= z <= 60
    assert all(x == 0 for x in flt[z:])
    assert ex.first_zero(exact) is None
    assert ex.first_zero([0.5, 0.25]) is None
