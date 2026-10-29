import math

import numpy as np

import non_euclidean_geometry_hyperbolic as ex


def test_vertical_distance_is_log():
    assert math.isclose(ex.hyp_dist(1j, math.e * 1j), 1.0)
    assert math.isclose(ex.hyp_dist(2j, 2j * math.exp(3)), 3.0)


def test_geodesics():
    assert ex.geodesic(1j, 3j) == ("vertical", 0.0)
    kind, c, r = ex.geodesic(-1 + 1j, 1 + 1j)
    assert kind == "circle" and math.isclose(c, 0.0) and math.isclose(r, math.sqrt(2))


def test_two_angle_methods_agree():
    rng = np.random.default_rng(1)
    for _ in range(40):
        pts = [complex(x, y) for x, y in zip(rng.uniform(-2, 2, 3), rng.uniform(0.2, 3, 3))]
        law = ex.angles_by_cosine_law(*pts)
        tan = ex.angles_by_tangents(*pts)
        assert max(abs(p - q) for p, q in zip(law, tan)) < 1e-7
        assert sum(law) < math.pi  # hyperbolic angle sum is less than pi


def test_mobius_preserves_distance_and_upper_half_plane():
    rng = np.random.default_rng(2)
    for _ in range(30):
        m = ex.random_sl2(rng)
        a, b, c, d = m
        assert math.isclose(a * d - b * c, 1.0)
        z, w = 0.5 + 1.2j, -1 + 0.4j
        gz, gw = ex.mobius(m, z), ex.mobius(m, w)
        assert gz.imag > 0 and gw.imag > 0
        assert math.isclose(ex.hyp_dist(z, w), ex.hyp_dist(gz, gw), rel_tol=1e-9)


def test_monte_carlo_area_matches_defect():
    rng = np.random.default_rng(4)
    z = (1j, 1 + 2j, -1 + 1.5j)
    est, se = ex.area_monte_carlo(*z, 200_000, rng)
    defect = math.pi - sum(ex.angles_by_cosine_law(*z))
    assert abs(est - defect) < 4 * se


def test_near_ideal_triangle_defect_below_pi():
    prev = 0
    for e in (0.5, 0.1, 0.01):
        d = math.pi - sum(ex.angles_by_cosine_law(-1 + e * 1j, 1 + e * 1j, 1j / e))
        assert prev < d < math.pi
        prev = d
