import math
from fractions import Fraction

import rigid_motions_similarity_dilations as rd


def test_dilate_and_centre():
    assert rd.dilate((2, 3), 2) == (4, 6)
    assert rd.dilate((2, -1), 5, centre=(2, -1)) == (2, -1)
    assert rd.dilate((4, 1), Fraction(1, 2), centre=(2, -1)) == (3, 0)


def test_area_and_lengths():
    tri = [(0, 0), (4, 0), (0, 3)]
    assert rd.area(tri) == 6
    assert rd.sq_len((0, 0), (3, 4)) == 25
    big = [rd.dilate(p, 3) for p in tri]
    assert rd.area(big) == 54 and rd.sq_len(big[1], big[2]) == 9 * 25


def test_angles():
    a = rd.angles([(0, 0), (4, 0), (0, 3)])
    assert math.isclose(sum(a), 180)
    assert math.isclose(a[0], 90)
    eq = rd.angles([(0, 0), (2, 0), (1, math.sqrt(3))])
    assert all(math.isclose(x, 60) for x in eq)


def test_every_check_passes_and_stretch_fails():
    tris = rd.random_triangles(40, seed=3)
    for k in (Fraction(1, 3), Fraction(5, 2)):
        assert rd.check(tris, k, (1, 1)) == (40, 40, 40, 40)
    tri = [(0, 0), (1, 0), (0, 1)]
    stretched = [rd.stretch_x(p, 2) for p in tri]
    assert not math.isclose(rd.angles(tri)[1], rd.angles(stretched)[1])


def test_parallel():
    assert rd.parallel((0, 0), (1, 2), (5, 5), (7, 9))
    assert not rd.parallel((0, 0), (1, 2), (0, 0), (2, 1))
