import pytest

import model_theory_ef_games as ef


def test_consistent_detects_order_and_equality():
    assert ef.consistent((), (0, 5))
    assert ef.consistent(((1, 1),), (2, 4))
    assert not ef.consistent(((1, 1),), (2, 0)), "order reversed"
    assert not ef.consistent(((1, 1),), (1, 2)), "equality not preserved"
    assert not ef.consistent(((1, 1),), (3, 1)), "distinct mapped to equal"


def test_trivial_games():
    assert ef.duplicator_wins(3, 7, 0), "zero rounds: Duplicator always wins"
    assert ef.duplicator_wins(5, 5, 4), "isomorphic orders"
    assert ef.duplicator_wins(1, 9, 1), "one round sees only nonemptiness"
    with pytest.raises(ValueError):
        ef.duplicator_wins(-1, 2, 1)


def test_spoiler_wins_small_differences():
    # Two rounds tell 2 elements from 3: Spoiler picks the middle of 3.
    assert not ef.duplicator_wins(2, 3, 2)
    # Three rounds tell 6 from 7, but not 7 from 8.
    assert not ef.duplicator_wins(6, 7, 3)
    assert ef.duplicator_wins(7, 8, 3)


@pytest.mark.parametrize("k,sizes", [(1, range(1, 7)), (2, range(1, 8)), (3, range(1, 10))])
def test_rule_matches_search(k, sizes):
    total, wrong = ef.check_range(k, list(sizes))
    assert total == len(sizes) * (len(sizes) + 1) // 2
    assert wrong == []


def test_symmetry_and_threshold():
    for m in range(1, 6):
        for n in range(1, 6):
            assert ef.duplicator_wins(m, n, 2) == ef.duplicator_wins(n, m, 2)
    assert [ef.smallest_equivalent_pair(k, 10) for k in (1, 2, 3)] == [1, 3, 7]
    assert ef.predicted(3, 100, 2) and not ef.predicted(2, 100, 2)
