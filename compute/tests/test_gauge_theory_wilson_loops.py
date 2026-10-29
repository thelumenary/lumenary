import cmath
import random

import pytest

import gauge_theory_wilson_loops as wl

ONE2 = [[1 + 0j, 0j], [0j, 1 + 0j]]


def close(a, b, tol=1e-12):
    return all(abs(a[i][j] - b[i][j]) < tol for i in range(2) for j in range(2))


def test_random_su2_is_special_unitary():
    rng = random.Random(3)
    for _ in range(50):
        u = wl.random_su2(rng)
        assert close(wl.mat_mul(u, wl.dagger(u)), ONE2)
        det = u[0][0] * u[1][1] - u[0][1] * u[1][0]
        assert det == pytest.approx(1)


def test_wilson_loops_gauge_invariant_but_holonomy_not():
    rng = random.Random(4)
    size = 5
    links = wl.grid_links(size, lambda x, y, d: wl.random_su2(rng))
    g = {(x, y): wl.random_su2(rng) for x in range(size + 1) for y in range(size + 1)}
    moved = wl.gauge(links, g, wl.mat_mul, wl.dagger)
    steps, start = wl.rectangle_path(0, 0, 3, 2)
    a = wl.holonomy(links, start, steps, wl.mat_mul, wl.dagger, ONE2)
    b = wl.holonomy(moved, start, steps, wl.mat_mul, wl.dagger, ONE2)
    assert wl.trace(a) == pytest.approx(wl.trace(b), abs=1e-12)
    # covariance: b = g(start) a g(start)^-1
    gs = g[start]
    assert close(b, wl.mat_mul(wl.mat_mul(gs, a), wl.dagger(gs)))
    assert not close(a, b, 1e-3)


def test_open_path_transforms_by_endpoints():
    rng = random.Random(8)
    size = 4
    links = wl.grid_links(size, lambda x, y, d: wl.random_su2(rng))
    g = {(x, y): wl.random_su2(rng) for x in range(size + 1) for y in range(size + 1)}
    moved = wl.gauge(links, g, wl.mat_mul, wl.dagger)
    steps = ["E", "E", "N", "W", "N"]
    a = wl.holonomy(links, (1, 0), steps, wl.mat_mul, wl.dagger, ONE2)
    b = wl.holonomy(moved, (1, 0), steps, wl.mat_mul, wl.dagger, ONE2)
    assert close(b, wl.mat_mul(wl.mat_mul(g[(1, 0)], a), wl.dagger(g[(2, 2)])))


@pytest.mark.parametrize("string", ["east", "north"])
def test_solenoid_is_flat_except_one_square(string):
    links = wl.solenoid_field(6, (2, 3), 0.7, string)
    curv = wl.plaquette_angles(links, 6)
    assert curv[(2, 3)] == pytest.approx(0.7)
    assert all(abs(t) < 1e-12 for p, t in curv.items() if p != (2, 3))


def test_aharonov_bohm_phase_depends_on_winding_only():
    mul, inv, one = wl.u1_ops()
    phi = 0.9
    for string in ["east", "north"]:
        links = wl.solenoid_field(8, (3, 3), phi, string)
        loop = ["E"] * 4 + ["N"] * 4 + ["W"] * 4 + ["S"] * 4
        assert cmath.phase(wl.holonomy(links, (1, 1), loop, mul, inv, one)) == pytest.approx(phi)
        big = ["E"] * 7 + ["N"] * 6 + ["W"] * 7 + ["S"] * 6
        assert cmath.phase(wl.holonomy(links, (0, 1), big, mul, inv, one)) == pytest.approx(phi)
        assert cmath.phase(wl.holonomy(links, (1, 1), loop * 2, mul, inv, one)) == pytest.approx(2 * phi)
        away = ["E"] * 2 + ["N"] * 2 + ["W"] * 2 + ["S"] * 2
        assert abs(cmath.phase(wl.holonomy(links, (5, 2), away, mul, inv, one))) < 1e-12
