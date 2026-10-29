import actions_and_undoing_tiny_worlds as tw


def test_number_of_actions_is_n_to_the_n():
    for n in range(1, 5):
        assert len(tw.all_actions(n)) == n ** n
    assert tw.all_actions(2) == [(0, 0), (0, 1), (1, 0), (1, 1)]


def test_do_nothing_is_neutral():
    for a in tw.all_actions(3):
        assert tw.then(tw.do_nothing(3), a) == a
        assert tw.then(a, tw.do_nothing(3)) == a


def test_flip_undoes_flip_and_go_round_needs_the_other_way():
    flip = (1, 0)
    assert tw.undoes(flip, flip)
    go_round = (1, 2, 0)
    assert not tw.undoes(go_round, go_round)
    assert tw.find_undo(go_round) == (2, 0, 1)
    assert tw.undoes(go_round, tw.find_undo(go_round))


def test_actions_with_a_collision_cannot_be_undone():
    squash = (0, 0, 2)  # things 0 and 1 both become 0
    assert not tw.no_two_the_same(squash)
    assert tw.find_undo(squash) is None


def test_rule_and_counts_exhaustively():
    expected = {1: (1, 1), 2: (2, 2), 3: (6, 4), 4: (24, 10)}
    for n, (undoable, self_undo) in expected.items():
        acts = tw.all_actions(n)
        can = [a for a in acts if tw.find_undo(a) is not None]
        assert len(can) == undoable
        assert all((a in can) == tw.no_two_the_same(a) for a in acts)
        assert sum(1 for a in acts if tw.undoes(a, a)) == self_undo


def test_quarter_turns():
    assert tw.quarter_turn("left") == "up"
    assert tw.turns_to_undo(tw.quarter_turn, "up") == 3
    assert tw.turns_to_undo(lambda x: x, "up") == 0


def test_describe():
    assert tw.describe((1, 2, 0)) == "0->1, 1->2, 2->0"
