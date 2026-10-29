import random

import projective_geometry_finite_planes as pfp


def test_point_counts():
    for p in (2, 3, 5):
        assert len(pfp.points(p)) == p * p + p + 1


def test_normalise():
    assert pfp.normalise([0, 3, 6], 7) == (0, 1, 2)
    assert pfp.normalise([2, 4, 6], 5) == (1, 2, 3)
    assert pfp.normalise([-1, 0, 0], 3) == (1, 0, 0)


def test_fano_plane_incidence():
    n, per_line, axioms = pfp.incidence_report(2)
    assert n == 7 and per_line == {3} and axioms


def test_cross_product_is_the_join():
    p = 5
    for u, v in [((1, 0, 0), (0, 1, 0)), ((1, 2, 3), (0, 1, 4))]:
        l = pfp.cross(u, v, p)
        assert pfp.dot(l, u, p) == 0 and pfp.dot(l, v, p) == 0
        assert any(l)


def test_collinear():
    p = 7
    assert pfp.collinear((1, 0, 0), (0, 1, 0), (1, 1, 0), p)
    assert not pfp.collinear((1, 0, 0), (0, 1, 0), (0, 0, 1), p)


def test_conic_has_p_plus_one_points():
    for p in (3, 5, 7, 11):
        assert pfp.conic_points(p) == p + 1


def test_desargues_and_pappus_hold_in_small_planes():
    rng = random.Random(5)
    assert all(pfp.desargues_trial(rng, 5) for _ in range(40))
    assert all(pfp.pappus_trial(rng, 5) for _ in range(40))
