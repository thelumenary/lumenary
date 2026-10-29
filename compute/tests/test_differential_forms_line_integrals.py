import math

import pytest

import differential_forms_line_integrals as li


def test_exact_form_has_zero_circulation():
    for p, v in (li.circle(0, 0, 1), li.circle(2, -1, 0.5), li.square_loop()):
        assert li.line_integral(li.exact_form, p, v) == pytest.approx(0, abs=1e-6)


def test_exact_form_integral_is_difference_of_potential():
    f = lambda x, y: x * x * y + math.sin(x * y)
    p, v = li.half_circle(True)
    assert li.line_integral(li.exact_form, p, v) == pytest.approx(f(-1, 0) - f(1, 0), abs=1e-6)


def test_dtheta_counts_winding():
    cases = [(li.circle(0, 0, 1), 1), (li.circle(0, 0, 2, turns=-1), -1),
             (li.circle(0, 0, 1, turns=3), 3), (li.circle(3, 0, 1), 0), (li.square_loop(), 1)]
    for (p, v), w in cases:
        assert li.line_integral(li.dtheta, p, v) == pytest.approx(2 * math.pi * w, abs=1e-5)


def test_dtheta_is_path_dependent():
    up = li.line_integral(li.dtheta, *li.half_circle(True))
    down = li.line_integral(li.dtheta, *li.half_circle(False))
    assert up == pytest.approx(math.pi, abs=1e-6)
    assert down == pytest.approx(-math.pi, abs=1e-6)


def test_green_area():
    assert li.line_integral(li.area_form, *li.circle(1, 1, 2)) == pytest.approx(2 * math.pi * 4, rel=1e-6)
    assert li.line_integral(li.area_form, *li.square_loop()) == pytest.approx(18, rel=1e-9)


def test_square_loop_is_closed_and_continuous():
    p, _ = li.square_loop()
    assert p(0) == (-1, -1)
    assert p(0.25) == pytest.approx((2, -1))
    assert p(0.999999) == pytest.approx((-1, -1), abs=1e-4)
