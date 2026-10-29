from fractions import Fraction

import coordinate_plane_reflections as cp


def test_reflection_formulas():
    assert cp.reflect_x((3, 2)) == (3, -2)
    assert cp.reflect_y((3, 2)) == (-3, 2)
    assert cp.half_turn((3, 2)) == (-3, -2)
    assert cp.swap((3, 2)) == (2, 3)
    p = (Fraction(1, 2), Fraction(-7, 3))
    assert cp.reflect_x(cp.reflect_x(p)) == p
    assert cp.reflect_x(cp.reflect_y(p)) == cp.half_turn(p) == cp.reflect_y(cp.reflect_x(p))


def test_quadrants_and_axes():
    assert [cp.quadrant(p) for p in [(1, 1), (-1, 1), (-1, -1), (1, -1)]] == [1, 2, 3, 4]
    assert cp.quadrant((0, 5)) == cp.quadrant((-2, 0)) == cp.quadrant((0, 0)) == 0
    mirror = {0: 0, 1: 4, 2: 3, 3: 2, 4: 1}
    for p in cp.grid_points(4):
        assert cp.quadrant(cp.reflect_x(p)) == mirror[cp.quadrant(p)]


def test_fixed_points_of_reflection_are_the_axis():
    pts = cp.grid_points(3)
    assert [p for p in pts if cp.reflect_x(p) == p] == [(a, 0) for a in range(-3, 4)]


def test_grid_distance():
    assert cp.grid_distance((-3, 2), (4, 2)) == 7
    assert cp.grid_distance((0, 0), (3, -4)) == 7
    assert cp.grid_distance((1, 1), (1, 1)) == 0
    pts = cp.grid_points(2)
    for p in pts:
        for q in pts:
            for r in pts:
                assert cp.grid_distance(p, r) <= cp.grid_distance(p, q) + cp.grid_distance(q, r)


def test_moves_keep_distance_but_stretch_does_not():
    pts = cp.grid_points(3)
    for move in (cp.reflect_x, cp.reflect_y, cp.half_turn, cp.swap):
        assert cp.keeps_distance(move, pts) == 0
    assert cp.keeps_distance(cp.stretch_x, pts) > 0


def test_lines_and_steps():
    assert cp.lines_and_steps(-3, 4) == (7, 8)
    assert cp.lines_and_steps(4, -3) == (7, 8)
    assert cp.lines_and_steps(2, 2) == (0, 1)
