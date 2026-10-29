import math

import numpy as np

import geometric_analysis_curve_shortening as cs


def circle(r, n=200):
    t = np.linspace(0.0, 2 * math.pi, n, endpoint=False)
    return np.stack([r * np.cos(t), r * np.sin(t)], axis=1)


def test_polygon_measurements():
    sq = np.array([[0.0, 0.0], [1.0, 0.0], [1.0, 1.0], [0.0, 1.0]])
    assert abs(cs.area(sq) - 1.0) < 1e-12
    assert abs(cs.length(sq) - 4.0) < 1e-12
    assert abs(cs.turning_angles(sq).sum() - 2 * math.pi) < 1e-12


def test_curvature_of_circle_points_inward_with_size_one_over_r():
    p = circle(2.0)
    k = cs.curvature_vectors(p)
    sizes = np.linalg.norm(k, axis=1)
    assert np.allclose(sizes, 0.5, rtol=1e-3)
    assert np.all(np.sum(k * p, axis=1) < 0)  # inward


def test_circle_shrinks_like_sqrt_r0_squared_minus_2t():
    p = cs.flow(circle(1.0, 120), 0.2)
    r = math.sqrt(cs.area(p) / math.pi)
    assert abs(r - math.sqrt(1 - 2 * 0.2)) < 5e-3


def test_area_decreases_at_rate_two_pi():
    p0 = cs.initial_curve()
    p1 = cs.flow(p0, 0.3)
    rate = (cs.area(p0) - cs.area(p1)) / 0.3
    assert abs(rate - 2 * math.pi) < 0.15


def test_curve_becomes_convex_and_round():
    p0 = cs.initial_curve()
    assert cs.turning_angles(p0).min() < 0
    p1 = cs.flow(p0, 0.3)
    assert cs.turning_angles(p1).min() > 0
    assert cs.length(p1) ** 2 / (4 * math.pi * cs.area(p1)) < 1.01


def test_redistribute_preserves_shape_of_a_circle():
    p = cs.redistribute(circle(1.0, 100))
    assert abs(cs.area(p) - cs.area(circle(1.0, 100))) < 1e-9
    assert np.allclose(np.linalg.norm(p, axis=1), 1.0, atol=1e-3)
