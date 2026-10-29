import symmetry_transformations_polygons as sp


def test_steps_apart():
    assert sp.steps_apart(6, 0, 1) == 1
    assert sp.steps_apart(6, 0, 5) == 1
    assert sp.steps_apart(6, 0, 3) == 3
    assert sp.steps_apart(5, 4, 1) == 2


def test_regular_polygons_have_n_turns_and_n_flips():
    for n in range(3, 8):
        turns, flips = sp.regular_polygon_symmetries(n)
        assert len(turns) == n and len(flips) == n
        assert tuple(range(n)) in turns  # doing nothing is a symmetry


def test_turns_keep_cyclic_order_and_flips_reverse_it():
    n = 6
    turns, flips = sp.regular_polygon_symmetries(n)
    for t in turns:
        assert all((t[(i + 1) % n] - t[i]) % n == 1 for i in range(n))
    for f in flips:
        assert all((f[(i + 1) % n] - f[i]) % n == n - 1 for i in range(n))


def test_quadrilaterals():
    expected = {
        "square": (4, 4), "rectangle": (2, 2), "rhombus": (2, 2),
        "kite": (1, 1), "parallelogram": (2, 0), "isosceles trapezium": (1, 1),
    }
    for name, (t, f) in expected.items():
        turns, flips = sp.quadrilateral_symmetries(sp.QUADRILATERALS[name])
        assert (len(turns), len(flips)) == (t, f), name


def test_rectangle_diagonal_swap_is_not_a_symmetry():
    rect = sp.QUADRILATERALS["rectangle"]
    turns, flips = sp.quadrilateral_symmetries(rect)
    # Swapping corners 0 and 2 (along a diagonal) while fixing 1 and 3:
    assert (2, 1, 0, 3) not in turns + flips
    square_turns, square_flips = sp.quadrilateral_symmetries(sp.QUADRILATERALS["square"])
    assert (2, 1, 0, 3) in square_flips


def test_irregular_quadrilateral_has_only_trivial_symmetry():
    corners = [(0, 0), (4, 0), (5, 3), (1, 2)]
    turns, flips = sp.quadrilateral_symmetries(corners)
    assert turns == [(0, 1, 2, 3)] and flips == []
    assert sp.cross((0, 0), (1, 0), (0, 1)) > 0
    assert sp.sq_dist((0, 0), (3, 4)) == 25
