from fractions import Fraction

import pytest

import point_set_topology_bisection_cover as bc


def test_smallest_index_above():
    assert bc.smallest_index_above(Fraction(1, 2)) == 3
    assert bc.smallest_index_above(Fraction(1, 3)) == 4
    assert bc.smallest_index_above(Fraction(2, 5)) == 3
    with pytest.raises(ValueError):
        bc.smallest_index_above(0)


def test_cover_membership():
    assert bc.cover_closed(Fraction(0), Fraction(1, 16)) == 0
    assert bc.cover_closed(Fraction(1, 2), Fraction(1)) == 3
    assert bc.cover_closed(Fraction(0), Fraction(1, 8)) is None
    assert bc.cover_half_open(Fraction(0), Fraction(1, 16), True) is None
    assert bc.cover_half_open(Fraction(1, 4), Fraction(1, 2)) == 5


def test_closed_interval_halts_with_valid_subcover():
    used, left, depth = bc.bisect_cover(bc.cover_closed, 0, 1, 60)
    assert left == [] and depth < 60
    assert used == [0, 3, 5, 9, 17]
    # the chosen sets really cover [0, 1]: check a fine grid of points
    def inside(x, n):
        return -Fraction(1, 10) < x < Fraction(1, 10) if n == 0 else Fraction(1, n) < x < 2
    for k in range(0, 1001):
        x = Fraction(k, 1000)
        assert any(inside(x, n) for n in used)


def test_half_open_interval_never_halts():
    for depth in (3, 7, 12):
        used, left, _ = bc.bisect_cover(bc.cover_half_open, 0, 1, depth, True)
        assert left == [(Fraction(0), Fraction(1, 2**depth))]
        assert len(used) == depth
        assert max(used) == 2**depth + 1


def test_finite_subfamilies_miss_points_near_zero():
    used, _, _ = bc.bisect_cover(bc.cover_half_open, 0, 1, 10, True)
    n_max = max(used)
    x = Fraction(1, 2 * n_max)
    assert all(not (Fraction(1, n) < x) for n in used)
