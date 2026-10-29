import math

import pytest

import mathematical_biology_logistic_map as ex


def test_logistic_and_orbit():
    assert ex.logistic(4.0, 0.5) == 1.0
    assert ex.orbit(2.0, 0.5, 3) == [0.5, 0.5, 0.5, 0.5]
    assert len(ex.orbit(3.0, 0.1, 10)) == 11


@pytest.mark.parametrize("r, period", [(2.8, 1), (3.2, 2), (3.5, 4), (3.56, 8), (3.83, 3)])
def test_attractor_periods(r, period):
    assert ex.attractor_period(r) == period


def test_chaotic_parameter_has_no_short_period():
    assert ex.attractor_period(4.0, x0=0.123) is None


def test_period_two_points_match_formula():
    r = 3.2
    s = math.sqrt((r - 3) * (r + 1))
    xp, xm = (r + 1 + s) / (2 * r), (r + 1 - s) / (2 * r)
    assert ex.logistic(r, xp) == pytest.approx(xm)
    assert ex.logistic(r, xm) == pytest.approx(xp)
    # multiplier -r^2 + 2r + 4
    mult = r * (1 - 2 * xp) * r * (1 - 2 * xm)
    assert mult == pytest.approx(-r * r + 2 * r + 4)


def test_superstable_parameters():
    rs = ex.superstable_parameters(7)
    assert rs[1] == pytest.approx(1 + math.sqrt(5))
    assert rs[2] == pytest.approx(3.4985616993, abs=1e-8)
    assert rs[3] == pytest.approx(3.5546408628, abs=1e-8)
    assert abs(ex.superstable_gap(rs[4], 4)) < 1e-10
    ratio = (rs[5] - rs[4]) / (rs[6] - rs[5])
    assert ratio == pytest.approx(4.6692, abs=0.002)


def test_lyapunov_signs():
    assert ex.lyapunov(3.2) < 0
    assert ex.lyapunov(3.7) > 0
    assert ex.lyapunov(4.0) == pytest.approx(math.log(2), abs=0.02)
