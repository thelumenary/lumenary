import adjunctions_formal_concepts as fc


def test_up_and_down():
    assert fc.up(frozenset({2, 4})) == frozenset({"even", "div12"})
    assert fc.down(frozenset({"odd", "prime"})) == frozenset({3, 5, 7})
    assert fc.up(frozenset()) == frozenset(fc.PROPERTIES)
    assert fc.down(frozenset()) == frozenset(fc.OBJECTS)


def test_subsets_count():
    assert len(fc.subsets([1, 2, 3])) == 8
    assert fc.subsets([]) == [frozenset()]


def test_galois_connection_holds():
    pairs, ok = fc.galois_holds()
    assert pairs == 256 * 64 and ok


def test_closure_properties():
    for S in fc.subsets(fc.OBJECTS):
        c = fc.down(fc.up(S))
        assert S <= c                      # unit: S <= down(up(S))
        assert fc.down(fc.up(c)) == c      # idempotent
        assert fc.up(c) == fc.up(S)        # up o down o up = up


def test_closed_sets_correspond():
    closed = fc.closed_objects()
    assert len(closed) == 19
    props = {fc.up(S) for S in closed}
    assert len(props) == 19
    assert all(fc.down(fc.up(S)) == S for S in closed)
    assert frozenset({2, 4, 6}) in closed and frozenset({2, 4}) not in closed
