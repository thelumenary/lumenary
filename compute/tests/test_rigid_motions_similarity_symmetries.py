import rigid_motions_similarity_symmetries as rs


def test_moves_on_a_point():
    assert rs.MOVES["R90"](1, 0) == (0, 1)
    assert rs.MOVES["R270"](0, 1) == (1, 0)
    assert rs.MOVES["Md"](3, -2) == (-2, 3)
    assert rs.MOVES["Ma"](3, -2) == (2, -3)


def test_table_values():
    t = rs.table()
    assert t[("Mx", "Md")] == "R90" and t[("Md", "Mx")] == "R270"
    assert t[("R90", "R90")] == "R180"
    assert t[("Mx", "My")] == "R180" == t[("My", "Mx")]
    assert all(t[(m, m)] == "R0" for m in rs.MIRROR_ANGLE)


def test_group_properties():
    t = rs.table()
    assert all(v in rs.NAMES for v in t.values())
    for a in rs.NAMES:
        assert t[("R0", a)] == a == t[(a, "R0")]
        assert sum(t[(a, b)] == "R0" for b in rs.NAMES) == 1
        # each row is a shuffle of the eight moves
        assert sorted(t[(a, b)] for b in rs.NAMES) == sorted(rs.NAMES)
    for a in rs.NAMES:
        for b in rs.NAMES:
            for c in rs.NAMES:
                assert t[(t[(a, b)], c)] == t[(a, t[(b, c)])]


def test_rotations_commute_but_not_everything():
    t = rs.table()
    rots = ["R0", "R90", "R180", "R270"]
    assert all(t[(a, b)] == t[(b, a)] for a in rots for b in rots)
    differ = [(a, b) for a in rs.NAMES for b in rs.NAMES if t[(a, b)] != t[(b, a)]]
    assert len(differ) == 24


def test_isometries_and_a_non_example():
    assert all(rs.keeps_distances(f) for f in rs.MOVES.values())
    assert not rs.keeps_distances(lambda x, y: (2 * x, y))
    assert rs.name_of(lambda x, y: (2 * x, y)) is None
