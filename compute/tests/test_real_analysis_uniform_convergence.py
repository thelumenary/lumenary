import math

import pytest

import real_analysis_uniform_convergence as ex


def test_grid_endpoints_and_size():
    xs = ex.grid(0.0, 1.0, 11)
    assert len(xs) == 11
    assert xs[0] == 0.0 and math.isclose(xs[-1], 1.0)
    with pytest.raises(ValueError):
        ex.grid(0.0, 1.0, 1)


def test_grid_sup_is_a_lower_bound_for_x_to_the_n():
    xs = ex.grid(0.0, 1.0, 1001)[:-1]
    for n in [1, 10, 100]:
        s = ex.grid_sup(lambda x: x ** n, xs)
        assert 0 < s < 1  # the true sup over [0, 1) is 1, never attained
    # On [0, 0.9] the sup is attained at 0.9.
    assert math.isclose(ex.grid_sup(lambda x: x ** 7, ex.grid(0, 0.9, 91)), 0.9 ** 7)


def test_spike_sup_matches_calculus_and_grid():
    for n in [1, 3, 10]:
        peak = 1 / (n * math.sqrt(2))
        assert math.isclose(ex.spike(n, peak), ex.spike_sup(n), rel_tol=1e-12)
        assert ex.grid_sup(lambda x: ex.spike(n, x), ex.grid(0, 1, 20001)) <= ex.spike_sup(n) + 1e-12
    assert ex.spike_sup(10) > ex.spike_sup(5)  # blows up, so not uniform


def test_spike_pointwise_limit_is_zero_but_integrals_tend_to_one():
    assert ex.spike(60, 0.5) < 1e-300 or ex.spike(60, 0.5) == 0.0
    assert ex.spike(5, 0.0) == 0.0
    for n in [1, 2, 7]:
        assert math.isclose(ex.midpoint_integral(lambda x: ex.spike(n, x), 0, 1, 4000),
                            ex.spike_integral(n), rel_tol=1e-4)
    assert math.isclose(ex.spike_integral(1), 1 - math.exp(-1))
    assert abs(ex.spike_integral(10) - 1) < 1e-40


def test_midpoint_rule_exact_for_linear_functions():
    assert math.isclose(ex.midpoint_integral(lambda x: 3 * x + 1, 0, 2, 7), 8.0)
