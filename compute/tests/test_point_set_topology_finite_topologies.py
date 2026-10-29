import point_set_topology_finite_topologies as ft


def test_counts_match_known_values():
    assert [len(ft.topologies(n)) for n in range(5)] == [1, 1, 4, 29, 355]


def test_census_columns():
    assert ft.census(2) == (4, 3, 1, 1, 3)
    assert ft.census(3) == (29, 19, 1, 1, 19)
    assert ft.census(4) == (355, 219, 1, 1, 233)


def test_is_topology_rejects_bad_families():
    # missing the whole set
    assert not ft.is_topology(2, {0, 1})
    # on three points, {a} and {b} are open but their union {a, b} is missing
    assert not ft.is_topology(3, {0, 0b001, 0b010, 0b111})
    assert ft.is_topology(3, {0, 0b001, 0b010, 0b011, 0b111})


def test_discrete_and_indiscrete():
    n = 3
    discrete = frozenset(range(1 << n))
    indiscrete = frozenset({0, (1 << n) - 1})
    assert ft.is_topology(n, discrete) and ft.is_topology(n, indiscrete)
    assert ft.is_hausdorff(n, discrete) and not ft.is_connected(n, discrete)
    assert ft.is_connected(n, indiscrete) and not ft.is_t0(n, indiscrete)


def test_sierpinski_space():
    s = frozenset({0b00, 0b01, 0b11})
    assert ft.is_topology(2, s)
    assert ft.closed_sets(2, s) == {0b00, 0b10, 0b11}
    assert ft.is_t0(2, s) and not ft.is_t1(2, s) and ft.is_connected(2, s)


def test_closed_sets_are_complements_and_form_a_cotopology():
    for t in ft.topologies(3):
        closed = ft.closed_sets(3, t)
        assert len(closed) == len(t)
        for a in closed:
            for b in closed:
                assert a & b in closed and a | b in closed


def test_finite_t1_spaces_are_discrete():
    for n in range(1, 5):
        t1 = [t for t in ft.topologies(n) if ft.is_t1(n, t)]
        assert t1 == [frozenset(range(1 << n))]


def test_show():
    assert ft.show(0) == "{}"
    assert ft.show(0b11) == "{a, b}"
