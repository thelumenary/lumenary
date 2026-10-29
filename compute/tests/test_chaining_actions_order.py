import chaining_actions_order as co

A = co.NUMBER_ACTIONS


def test_chain_is_first_then_second():
    assert co.chain(A["add 5"], A["double"])(3) == 16
    assert co.chain(A["double"], A["add 5"])(3) == 11


def test_additions_and_multiplications_commute():
    assert co.first_difference(A["add 2"], A["add 5"]) is None
    assert co.first_difference(A["double"], A["triple"]) is None
    for f in A.values():
        assert co.first_difference(f, A["do nothing"]) is None


def test_mixed_pairs_differ_and_where():
    assert co.first_difference(A["add 5"], A["double"]) == 0
    assert co.first_difference(A["double"], A["square"]) == 1  # 0 works: (2*0)^2 = 2*0^2
    assert co.first_difference(A["add 2"], A["square"]) == 0


def test_tile_moves():
    M = co.MOVES
    assert not co.moves_commute(M["quarter turn"], M["flip left-right"])
    assert not co.moves_commute(M["quarter turn"], M["flip up-down"])
    assert co.moves_commute(M["flip left-right"], M["flip up-down"])
    for g in M.values():
        assert co.moves_commute(M["half turn"], g)


def test_four_quarter_turns_do_nothing():
    q = co.MOVES["quarter turn"]
    four = co.chain(co.chain(q, q), co.chain(q, q))
    assert co.place(four) == frozenset(co.L_SHAPE)
    assert co.place(q) != frozenset(co.L_SHAPE)
