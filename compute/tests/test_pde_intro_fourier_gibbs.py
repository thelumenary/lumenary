import math

import pytest

import pde_intro_fourier_gibbs as ex


def test_partial_sums_vanish_at_the_jump_and_are_odd():
    for n in [1, 7, 30]:
        assert ex.square_partial(0.0, n) == 0.0
        assert math.isclose(ex.square_partial(-0.3, n), -ex.square_partial(0.3, n))


def test_peak_is_a_local_maximum():
    for n in [5, 20, 80]:
        x = math.pi / (2 * n)
        h = x / 50
        peak = ex.square_partial(x, n)
        assert peak >= ex.square_partial(x - h, n)
        assert peak >= ex.square_partial(x + h, n)


def test_gibbs_constant():
    g = ex.gibbs_limit()
    assert abs(g - 1.1789797444721672) < 1e-9
    assert abs(ex.first_peak(2000) - g) < 1e-6
    # the overshoot does not disappear: every peak exceeds 1.178
    assert all(ex.first_peak(n) > 1.178 for n in [10, 100, 1000])


def test_sine_integral():
    assert ex.sine_integral(0.0, 2) == 0.0
    assert abs(ex.sine_integral(1.0) - 0.9460830703671830) < 1e-12
    with pytest.raises(ValueError):
        ex.sine_integral(1.0, 3)


def test_sawtooth_coefficients_match_numerical_integration():
    for n in [1, 2, 5]:
        steps = 20000
        h = 2 * math.pi / steps
        approx = sum((-math.pi + (i + 0.5) * h) * math.sin(n * (-math.pi + (i + 0.5) * h))
                     for i in range(steps)) * h / math.pi
        assert abs(approx - ex.sawtooth_coefficient(n)) < 1e-6


def test_parseval_partial_sums_approach_basel():
    errors = [math.pi ** 2 / 6 - ex.parseval_partial(N) for N in (10, 100, 1000)]
    assert all(e > 0 for e in errors)
    assert errors == sorted(errors, reverse=True)
    assert abs(1000 * errors[-1] - 1) < 0.01
