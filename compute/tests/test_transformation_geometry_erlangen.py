import random
from fractions import Fraction

import transformation_geometry_erlangen as ex

F = Fraction


def test_rational_rotation_is_orthogonal():
    rng = random.Random(1)
    for _ in range(20):
        c, s = ex.rational_rotation(rng)
        assert c * c + s * s == 1


def test_det_and_random_maps_are_invertible():
    assert ex.det3([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) == 1
    assert ex.det3([[1, 2, 3], [4, 5, 6], [7, 8, 9]]) == 0
    rng = random.Random(2)
    for group in ("euclidean", "similarity", "affine", "projective"):
        for _ in range(10):
            assert ex.det3(ex.random_map(rng, group)) != 0


def test_cross_ratio_and_param():
    assert ex.cross_ratio(F(0), F(1), F(2), F(3)) == F(2 * 2, 1 * 3)
    a, b = (F(0), F(0)), (F(2), F(4))
    assert ex.param(a, b, (F(1), F(2))) == F(1, 2)
    assert ex.param(a, b, (F(-2), F(-4))) == -1


def test_configuration_incidences():
    rng = random.Random(5)
    for _ in range(20):
        a, b, c, d, e, f, g, h = ex.random_configuration(rng)
        assert ex.cross(ex.sub(b, a), ex.sub(c, a)) == 0
        assert ex.cross(ex.sub(b, a), ex.sub(d, a)) == 0
        assert ex.cross(ex.sub(h, e), ex.sub(g, f)) == 0
        assert ex.cross(ex.sub(f, e), ex.sub(g, e)) != 0


def test_survival_table_matches_klein_hierarchy():
    rng = random.Random(1872)
    euc = ex.survival(rng, "euclidean", 30)
    assert all(v == 30 for v in euc.values())
    sim = ex.survival(rng, "similarity", 30)
    assert sim["distance"] == 0 and sim["angle"] == 30 and sim["cross-ratio"] == 30
    aff = ex.survival(rng, "affine", 30)
    assert aff["parallelism"] == 30 and aff["ratio on a line"] == 30
    assert aff["angle"] < 30
    proj = ex.survival(rng, "projective", 30)
    assert proj["collinearity"] == 30 and proj["cross-ratio"] == 30
    assert proj["ratio on a line"] < 30


def test_projective_map_preserves_cross_ratio_explicitly():
    m = [[1, 2, 0], [0, 1, 1], [1, 0, 3]]
    pts = [(F(t), F(2 * t)) for t in (0, 1, 3, -1)]
    img = [ex.act(m, p) for p in pts]
    assert None not in img
    before = ex.cross_ratio(*(ex.param(pts[0], pts[1], p) for p in pts))
    after = ex.cross_ratio(*(ex.param(img[0], img[1], p) for p in img))
    assert before == after
