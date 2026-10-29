import area_angles_rectangles as ar


def test_rectangles_with_perimeter():
    rects = ar.rectangles_with_perimeter(24)
    assert rects == [(1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6)]
    assert all(2 * (w + h) == 24 for w, h in rects)
    assert max(rects, key=lambda r: r[0] * r[1]) == (6, 6)
    assert ar.rectangles_with_perimeter(7) == []
    assert ar.rectangles_with_perimeter(4) == [(1, 1)]


def test_rectangles_with_area():
    rects = ar.rectangles_with_area(24)
    assert rects == [(1, 24), (2, 12), (3, 8), (4, 6)]
    assert ar.rectangles_with_area(1) == [(1, 1)]
    assert ar.rectangles_with_area(36)[-1] == (6, 6)


def test_perimeter_of_rectangles_matches_formula():
    for w in range(1, 9):
        for h in range(1, 9):
            squares = [(x, y) for x in range(w) for y in range(h)]
            assert ar.perimeter(squares) == 2 * (w + h)


def test_perimeter_of_other_shapes():
    assert ar.perimeter([(0, 0)]) == 4
    l_shape = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0)]
    assert ar.perimeter(l_shape) == 12
    plus = [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)]
    assert ar.perimeter(plus) == 12
    p_shape = [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2)]
    assert ar.perimeter(p_shape) == 10


def test_normalise_slides_shapes():
    assert ar.normalise([(3, 5), (4, 5)]) == frozenset({(0, 0), (1, 0)})


def test_known_counts_of_shapes():
    # Fixed polyominoes: 1, 2, 6, 19, 63 shapes of size 1..5.
    assert [len(ar.shapes_of_size(n)) for n in range(1, 6)] == [1, 2, 6, 19, 63]
    for shape in ar.shapes_of_size(4):
        assert len(shape) == 4
        assert ar.perimeter(shape) in (8, 10)
