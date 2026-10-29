import math

import dynamical_systems_logistic as ex


def test_logistic_step_and_fixed_point():
    assert ex.logistic(3.0, 0.5) == 0.75
    r = 2.5
    x = 1 - 1 / r
    assert math.isclose(ex.logistic(r, x), x)


def test_attractor_periods_match_theory():
    assert ex.attractor_period(2.8) == 1   # 1 < r < 3: fixed point 1 - 1/r
    assert ex.attractor_period(3.2) == 2   # 3 < r < 1 + sqrt(6)
    assert ex.attractor_period(3.5) == 4
    assert ex.attractor_period(3.83) == 3  # the period-3 window
    assert ex.attractor_period(3.9) is None


def test_superstable_parameters():
    rs = ex.superstable_parameters(7)
    assert rs[0] == 2.0 and math.isclose(rs[1], 1 + math.sqrt(5))
    assert abs(rs[2] - 3.4985616993) < 1e-9
    assert all(a < b for a, b in zip(rs, rs[1:]))
    # x = 1/2 is periodic with period 2^n at R_n
    for n, r in enumerate(rs):
        g, _ = ex.superstable_residual(r, n)
        assert abs(g) < 1e-9


def test_feigenbaum_ratio_estimates():
    rs = ex.superstable_parameters(9)
    ratios = [(rs[n - 1] - rs[n - 2]) / (rs[n] - rs[n - 1]) for n in range(2, 9)]
    assert abs(ratios[-1] - 4.6692016) < 1e-3
    assert abs(ratios[-1] - 4.6692016) < abs(ratios[0] - 4.6692016)


def test_lyapunov_exponents():
    # at r = 2.8 the attracting fixed point has multiplier 2 - r = -0.8
    assert abs(ex.lyapunov_exponent(2.8) - math.log(0.8)) < 1e-6
    assert abs(ex.lyapunov_exponent(4.0) - math.log(2)) < 0.02
    assert ex.lyapunov_exponent(3.83) < 0 < ex.lyapunov_exponent(3.9)
