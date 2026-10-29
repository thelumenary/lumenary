from itertools import product

import symmetry_transformations_moves as sm


def test_basic_moves():
    assert sm.flip_v((2, 3)) == (-2, 3)
    assert sm.flip_h((2, 3)) == (2, -3)
    assert sm.flip_d((2, 3)) == (3, 2)
    assert sm.quarter_turn((1, 0)) == (0, 1)
    assert sm.half_turn((2, 3)) == (-2, -3)
    assert sm.slide(3, -1, (0, 0)) == (3, -1)
    assert sm.flip_at(2, (1, 5)) == (3, 5)


def test_undoing_moves():
    for p in product(range(-5, 6), repeat=2):
        assert sm.flip_v(sm.flip_v(p)) == p
        assert sm.flip_d(sm.flip_d(p)) == p
        q = p
        for _ in range(4):
            q = sm.quarter_turn(q)
        assert q == p
        assert sm.slide(-2, 7, sm.slide(2, -7, p)) == p


def test_two_flips():
    for p in product(range(-5, 6), repeat=2):
        assert sm.flip_h(sm.flip_v(p)) == sm.half_turn(p)
        assert sm.flip_v(sm.flip_d(p)) == sm.quarter_turn(p)
        for c, d in [(0, 1), (1, 4), (-2, 3)]:
            assert sm.flip_at(d, sm.flip_at(c, p)) == sm.slide(2 * (d - c), 0, p)


def test_order_matters():
    p = (1, 0)
    assert sm.flip_v(sm.quarter_turn(p)) != sm.quarter_turn(sm.flip_v(p))


def test_letters_and_pictures():
    f, h = sm.LETTERS["F"], sm.LETTERS["H"]
    assert len(f) == 8 and len(h) == 11
    assert sm.move_shape(sm.flip_v, h) == h == sm.move_shape(sm.half_turn, h)
    assert sm.move_shape(sm.flip_v, f) != sm.move_shape(sm.half_turn, f)
    assert sm.picture(f)[0] == "###"
    assert sm.picture(sm.move_shape(sm.half_turn, f))[-1] == "###"


def test_grid_checks_all_true():
    assert all(sm.check_on_grid(4).values())
    assert sm.dist2((0, 0), (3, 4)) == 25
