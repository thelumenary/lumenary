import math

import pytest

import smooth_manifolds_stokes_periods as sp


def test_stokes_on_disc():
    exact = 3 * math.pi / 4
    lhs = sp.line_integral(lambda x, y: (0.0, x**3), sp.circle(0, 0, 1))
    rhs = sp.disc_integral(lambda x, y: 3 * x * x, n_r=200, n_t=200)
    assert lhs == pytest.approx(exact, abs=1e-10)
    assert rhs == pytest.approx(exact, abs=1e-4)


def test_area_form_gives_area():
    # (x dy - y dx)/2 has d = dx^dy, so its boundary integral is the area pi.
    area = sp.line_integral(lambda x, y: (-y / 2, x / 2), sp.circle(0, 0, 1))
    assert area == pytest.approx(math.pi, abs=1e-10)
    assert sp.disc_integral(lambda x, y: 1.0, 100, 100) == pytest.approx(math.pi, abs=1e-3)


@pytest.mark.parametrize(
    "loop, winding",
    [
        (sp.circle(0, 0, 1), 1),
        (sp.circle(0, 0, 0.01), 1),
        (sp.ellipse(3, 0.2), 1),
        (sp.circle(0, 0, 1, turns=2), 2),
        (sp.circle(0, 0, 1, turns=-1), -1),
        (sp.circle(3, 0, 1), 0),
    ],
)
def test_periods_of_dtheta_are_winding_numbers(loop, winding):
    period = sp.line_integral(sp.angle_form(), loop)
    assert period / (2 * math.pi) == pytest.approx(winding, abs=1e-6)


def test_exact_form_has_zero_period():
    # d(x^2 y) = 2xy dx + x^2 dy integrates to 0 round any closed loop.
    form = lambda x, y: (2 * x * y, x * x)
    assert sp.line_integral(form, sp.ellipse(2, 1)) == pytest.approx(0, abs=1e-9)


def test_two_puncture_periods():
    form = sp.combine(2.0, sp.angle_form(-1, 0), -0.5, sp.angle_form(1, 0))
    left = sp.line_integral(form, sp.circle(-1, 0, 0.5)) / (2 * math.pi)
    right = sp.line_integral(form, sp.circle(1, 0, 0.5)) / (2 * math.pi)
    both = sp.line_integral(form, sp.circle(0, 0, 3)) / (2 * math.pi)
    assert left == pytest.approx(2.0, abs=1e-6)
    assert right == pytest.approx(-0.5, abs=1e-6)
    assert both == pytest.approx(left + right, abs=1e-6)
