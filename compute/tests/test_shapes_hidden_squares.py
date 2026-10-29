import pytest

import shapes_hidden_squares as hs


def test_grid_has_n_squared_dots():
    assert hs.grid(1) == [(0, 0)]
    assert len(hs.grid(4)) == 16
    assert (3, 3) in hs.grid(4) and (4, 0) not in hs.grid(4)
    with pytest.raises(ValueError):
        hs.grid(0)


def test_quarter_turn_four_times_is_doing_nothing():
    v = (2, -3)
    w = v
    for _ in range(4):
        w = hs.quarter_turn(w)
    assert w == v
    assert hs.quarter_turn((1, 0)) == (0, 1)


@pytest.mark.parametrize("n, total, upright", [(1, 0, 0), (2, 1, 1), (3, 6, 5), (4, 20, 14), (5, 50, 30)])
def test_square_counts(n, total, upright):
    found = hs.squares_on_grid(n)
    assert len(found) == total
    assert sum(1 for sq in found if hs.is_upright(sq)) == upright


def test_every_found_square_really_is_a_square():
    for sq in hs.squares_on_grid(5):
        pts = sorted(sq)
        assert len(pts) == 4
        d = sorted((a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2 for i, a in enumerate(pts) for b in pts[i + 1:])
        # four equal sides and two equal diagonals, each diagonal twice a side
        assert d[0] == d[1] == d[2] == d[3] > 0
        assert d[4] == d[5] == 2 * d[0]


def test_tilted_square_side_lengths():
    diamond = frozenset({(1, 0), (2, 1), (1, 2), (0, 1)})
    assert diamond in hs.squares_on_grid(3)
    assert not hs.is_upright(diamond)
    assert hs.side_squared(diamond) == 2
    assert hs.side_squared(frozenset({(0, 0), (3, 0), (3, 3), (0, 3)})) == 9


def test_turning_the_grid_keeps_squares():
    for n in range(2, 6):
        assert hs.turned_squares_are_squares(n)
    sq = frozenset({(0, 0), (1, 0), (1, 1), (0, 1)})
    assert hs.turn_grid(sq, 3) == frozenset({(2, 0), (2, 1), (1, 1), (1, 0)})


def test_formula_and_box_count_agree_with_search():
    for n in range(1, 8):
        assert hs.formula(n) == hs.count_by_bounding_box(n) == len(hs.squares_on_grid(n))
