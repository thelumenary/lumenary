import math

import geometric_analysis_catenoid as c


def test_critical_values():
    assert abs(c.S_STAR - 1.19967864) < 1e-7
    assert abs(c.S_STAR * math.tanh(c.S_STAR) - 1) < 1e-10
    assert abs(c.CRITICAL_RATIO - 0.66274342) < 1e-7
    assert abs(c.goldschmidt_ratio() - 0.52769740) < 1e-6


def test_catenoids_pass_through_the_rings():
    for h in (0.1, 0.3, 0.5, 0.65):
        fat, thin = c.catenoid_parameters(h, 1.0)
        assert fat > thin > 0
        for a in (fat, thin):
            assert abs(a * math.cosh(h / a) - 1.0) < 1e-9


def test_no_catenoid_beyond_critical_ratio():
    assert c.catenoid_parameters(0.67, 1.0) == ()
    assert c.catenoid_parameters(2.0, 1.0) == ()


def test_thin_catenoid_has_more_area():
    for h in (0.1, 0.3, 0.5, 0.6, 0.66):
        fat, thin = c.catenoid_parameters(h, 1.0)
        assert c.catenoid_area(thin, h) > c.catenoid_area(fat, h)


def test_area_formula_against_numerical_integration():
    a, h, n = 0.7, 0.4, 20000
    dx = 2 * h / n
    total = sum(2 * math.pi * a * math.cosh((-h + (k + 0.5) * dx) / a) ** 2 * dx
                for k in range(n))
    assert abs(total - c.catenoid_area(a, h)) < 1e-6


def test_euler_lagrange_residual_vanishes():
    for a in (0.2, 1.0, 3.0):
        for x in (-1.0, 0.0, 0.7):
            assert abs(c.euler_lagrange_residual(a, x)) < 1e-9
