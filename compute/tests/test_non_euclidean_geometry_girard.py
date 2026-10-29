import math

import numpy as np

import non_euclidean_geometry_girard as ex


def test_from_lat_lon_unit_vectors():
    for lat, lon in [(0, 0), (90, 0), (-33.9, 151.2)]:
        assert math.isclose(np.linalg.norm(ex.from_lat_lon(lat, lon)), 1.0)
    assert np.allclose(ex.from_lat_lon(90, 0), [0, 0, 1])


def test_octant_triangle():
    a, b, c = (ex.from_lat_lon(*p) for p in ((90, 0), (0, 0), (0, 90)))
    for p, q, r in ((a, b, c), (b, c, a), (c, a, b)):
        assert math.isclose(ex.vertex_angle(p, q, r), math.pi / 2)
    assert math.isclose(ex.angle_excess(a, b, c), math.pi / 2)
    assert math.isclose(ex.exact_area(a, b, c), 4 * math.pi / 8)


def test_excess_equals_exact_area_on_random_triangles():
    rng = np.random.default_rng(0)
    for _ in range(50):
        a, b, c = (ex.unit(v) for v in rng.normal(size=(3, 3)))
        assert math.isclose(ex.angle_excess(a, b, c), ex.exact_area(a, b, c),
                            rel_tol=1e-7, abs_tol=1e-9)


def test_monte_carlo_within_error():
    rng = np.random.default_rng(5)
    a, b, c = (ex.from_lat_lon(*p) for p in ((90, 0), (0, 0), (0, 90)))
    est, se = ex.monte_carlo_area(a, b, c, 100_000, rng)
    assert se > 0
    assert abs(est - math.pi / 2) < 4 * se


def test_law_of_cosines_and_small_triangles():
    rng = np.random.default_rng(3)
    for _ in range(30):
        a, b, c = (ex.unit(v) for v in rng.normal(size=(3, 3)))
        assert ex.law_of_cosines_gap(a, b, c) < 1e-9
    a, b, c = (ex.from_lat_lon(*p) for p in ((0, 0), (0, 0.1), (0.1, 0)))
    assert 0 < ex.angle_excess(a, b, c) < 1e-5  # nearly flat
