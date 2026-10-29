import math

import pytest

import multivariable_calculus_green_circulation as gc


def test_circulation_of_rotation_field_is_twice_area():
    # F = (-y, x) has curl 2, so the circulation is 2 * area = 2 pi r^2.
    P = lambda x, y: -y
    Q = lambda x, y: x
    for r in [0.5, 1, 2]:
        assert gc.circulation(P, Q, (0.3, -1), r) == pytest.approx(2 * math.pi * r * r)


def test_gradient_field_has_zero_circulation():
    # F = grad(x^2 y) = (2xy, x^2) is conservative.
    P = lambda x, y: 2 * x * y
    Q = lambda x, y: x * x
    assert abs(gc.circulation(P, Q, (1, 2), 1.5)) < 1e-9


def test_green_holds_for_smooth_field():
    circ = gc.circulation(gc.smooth_P, gc.smooth_Q, (0, 0), 1)
    inner = gc.disc_integral(gc.smooth_curl, (0, 0), 1)
    assert circ == pytest.approx(1.5 * math.pi, rel=1e-9)
    assert inner == pytest.approx(1.5 * math.pi, rel=1e-4)


def test_vortex_circulation_is_two_pi_on_every_circle_round_the_origin():
    for r in [0.001, 0.5, 3]:
        assert gc.circulation(gc.vortex_P, gc.vortex_Q, (0, 0), r) == pytest.approx(2 * math.pi)
    # A circle around the origin that is not centred there.
    assert gc.circulation(gc.vortex_P, gc.vortex_Q, (0.4, 0.2), 1) == pytest.approx(2 * math.pi)
    # A circle that does not enclose the origin.
    assert abs(gc.circulation(gc.vortex_P, gc.vortex_Q, (2, 0), 1)) < 1e-9


def test_vortex_curl_is_zero_numerically():
    h = 1e-5
    for (x, y) in [(1, 0), (0.3, -0.7), (-2, 1.5)]:
        qx = (gc.vortex_Q(x + h, y) - gc.vortex_Q(x - h, y)) / (2 * h)
        py = (gc.vortex_P(x, y + h) - gc.vortex_P(x, y - h)) / (2 * h)
        assert abs(qx - py) < 1e-6
        assert gc.vortex_curl(x, y) == 0.0


def test_disc_integral_of_one_is_area():
    assert gc.disc_integral(lambda x, y: 1.0, (5, 5), 2, n_r=50, n_t=50) == pytest.approx(4 * math.pi)
