import math
from fractions import Fraction

import numerical_methods_floating_point as fp


def test_machine_epsilon():
    eps = fp.machine_epsilon()
    assert eps == 2.0 ** -52
    assert 1.0 + eps > 1.0
    assert 1.0 + eps / 2 == 1.0


def test_point_one_is_not_one_tenth():
    assert Fraction(0.1) != Fraction(1, 10)
    assert abs(Fraction(0.1) - Fraction(1, 10)) < Fraction(1, 10) * Fraction(2) ** -53


def test_series_matches_formula_for_moderate_x():
    for x in (0.5, 1.0, 2.0):
        assert math.isclose(fp.one_minus_cos_series(x, 20), (1 - math.cos(x)) / x ** 2,
                            rel_tol=1e-13)


def test_cancellation_naive_vs_stable():
    x = 1e-8
    exact = fp.one_minus_cos_series(x)
    assert fp.naive_one_minus_cos(x) == 0.0  # every digit lost
    assert fp.relative_error(fp.stable_one_minus_cos(x), exact) < 1e-15


def test_quadratic_roots():
    big, small = fp.quadratic_roots_stable(-1e8, 1.0)
    assert math.isclose(big * small, 1.0, rel_tol=1e-15)
    assert math.isclose(small, 1e-8, rel_tol=1e-15)
    naive_small = fp.quadratic_roots_naive(-1e8, 1.0)[1]
    assert fp.relative_error(naive_small, 1e-8) > 0.1
    # a well-conditioned case: both formulas agree
    r1, r2 = fp.quadratic_roots_naive(-3.0, 2.0)
    s1, s2 = fp.quadratic_roots_stable(-3.0, 2.0)
    assert (r1, r2) == (2.0, 1.0) and (s1, s2) == (2.0, 1.0)
