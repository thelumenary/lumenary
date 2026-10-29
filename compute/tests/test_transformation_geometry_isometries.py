import random
from fractions import Fraction

import transformation_geometry_isometries as ex

F = Fraction


def test_unit_from_slope_is_on_unit_circle():
    for t in [0, 1, 2, F(1, 2), -3, F(-5, 7)]:
        x, y = ex.unit_from_slope(t)
        assert x * x + y * y == 1
    assert ex.unit_from_slope(0) == (1, 0)
    assert ex.unit_from_slope(1) == (0, 1)  # line y = x: doubled direction is i


def test_reflection_fixes_its_mirror_and_is_an_involution():
    p = (F(1), F(2))
    e = ex.unit_from_slope(F(1, 2))  # mirror through p with slope 1/2
    r = ex.reflection(p, e)
    assert ex.classify(r) == "reflection"
    for s in range(-3, 4):
        q = (p[0] + 2 * s, p[1] + s)  # on the mirror
        assert ex.apply(r, q) == q
    z = (F(5), F(-1))
    assert ex.apply(r, ex.apply(r, z)) == z
    assert ex.classify(ex.compose(r, r)) == "identity"


def test_two_reflections():
    s1 = ex.reflection(ex.ZERO, ex.ONE)  # x-axis
    s2 = ex.reflection(ex.ZERO, ex.unit_from_slope(1))  # y = x
    rot = ex.compose(s2, s1)
    assert ex.classify(rot) == "rotation"
    assert rot[0] == (0, 1)  # rotation by 90 degrees = twice 45
    up = ex.reflection((F(0), F(3)), ex.ONE)  # y = 3
    tr = ex.compose(up, s1)
    assert ex.classify(tr) == "translation"
    assert tr[1] == (0, 6)


def test_compose_matches_pointwise_application():
    rng = random.Random(3)
    for _ in range(50):
        f, g = ex.random_reflection(rng), ex.random_reflection(rng)
        h = ex.compose(ex.compose(f, g), ex.random_reflection(rng))
        z = (F(rng.randint(-9, 9)), F(rng.randint(-9, 9)))
        fg = ex.compose(f, g)
        assert ex.apply(fg, z) == ex.apply(f, ex.apply(g, z))
        assert ex.classify(h) in ("reflection", "glide")


def test_glide_has_no_fixed_point_and_classification_is_consistent():
    glide = (ex.ONE, ex.ONE, True)  # z -> conj(z) + 1
    assert ex.classify(glide) == "glide"
    assert ex.fixed_point_check(glide)
    for z in [(F(0), F(0)), (F(1, 2), F(3)), (F(-4), F(0))]:
        assert ex.apply(glide, z) != z


def test_census_parity():
    rng = random.Random(11)
    for k in range(1, 5):
        counts, ok = ex.census(rng, k, 60)
        assert ok
        assert sum(counts.values()) == 60
        direct = {"identity", "translation", "rotation"}
        if k % 2 == 0:
            assert set(counts) <= direct
        else:
            assert set(counts) <= {"reflection", "glide"}
