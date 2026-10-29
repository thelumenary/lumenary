import math

import pde_intro_heat_scheme as ex


def test_exact_solution_initial_and_boundary_values():
    for x in [0.3, 1.0, 2.5]:
        assert abs(ex.exact(0.0, x, terms=2000) - x * (math.pi - x)) < 1e-6
    assert abs(ex.exact(0.7, 0.0)) < 1e-15
    assert abs(ex.exact(0.7, math.pi)) < 1e-12


def test_exact_solution_decays_like_first_mode():
    t = 2.0
    ratio = ex.exact(t, math.pi / 2) / (8 / math.pi * math.exp(-t))
    assert abs(ratio - 1) < 1e-3


def test_step_is_an_average_when_r_at_most_half():
    u = [0.0, 1.0, -2.0, 3.0, 0.5, 0.0]
    for r in [0.0, 0.25, 0.5]:
        new = ex.step(u, r)
        assert new[0] == 0.0 and new[-1] == 0.0
        assert max(new) <= max(u) + 1e-15 and min(new) >= min(u) - 1e-15
    assert ex.step(u, 0.0) == u


def test_stable_scheme_is_accurate_and_converges_at_second_order():
    e10 = ex.max_error(10, 0.4, 0.5)
    e20 = ex.max_error(20, 0.4, 0.5)
    assert e20 < 3e-3
    assert 3.5 < e10 / e20 < 4.5


def test_unstable_scheme_violates_maximum_principle():
    _, _, _, top = ex.solve(20, 0.6, 0.5)
    assert top > (math.pi / 2) ** 2
    _, _, _, top_ok = ex.solve(20, 0.5, 0.5)
    assert top_ok <= (math.pi / 2) ** 2 + 1e-12
