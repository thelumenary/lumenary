import pytest

import patterns_predict as pp


def test_item_follows_the_unit():
    assert [pp.item(pp.UNIT, n) for n in range(1, 7)] == ["red", "blue", "green"] * 2
    assert pp.item(pp.UNIT, 100) == "red"
    assert pp.item(pp.UNIT, 99) == "green"
    assert pp.item(("clap", "clap", "stamp"), 12) == "stamp"
    with pytest.raises(ValueError):
        pp.item(pp.UNIT, 0)


def test_remainder_shortcut_matches_drawing():
    for unit in [("a",), ("a", "b"), pp.UNIT, ("x", "y", "y", "z")]:
        drawn = pp.draw(unit, 500)
        assert len(drawn) == 500
        assert all(pp.item(unit, n) == drawn[n - 1] for n in range(1, 501))
        # The item k places further on is the same, k = length of the unit.
        k = len(unit)
        assert all(pp.item(unit, n + k) == pp.item(unit, n) for n in range(1, 400))


def test_smallest_unit_length():
    assert pp.smallest_unit_length(pp.draw(pp.UNIT, 60)) == 3
    assert pp.smallest_unit_length(pp.draw(("a", "b", "a", "b"), 40)) == 2
    assert pp.smallest_unit_length(pp.draw(("x", "y", "y"), 30)) == 3
    assert pp.smallest_unit_length(["a"] * 10) == 1
    assert pp.smallest_unit_length([1, 2, 3]) == 3


def test_growing_pattern_two_descriptions_agree():
    assert pp.add_two(0) == []
    assert pp.add_two(4) == [2, 4, 6, 8]
    assert pp.add_two(50) == [2 * n for n in range(1, 51)]


def test_same_start_different_rules():
    assert [pp.doubling(n) for n in range(1, 8)] == [1, 2, 4, 8, 16, 32, 64]
    assert [pp.add_more(n) for n in range(1, 8)] == [1, 2, 4, 7, 11, 16, 22]
    assert [pp.circle_regions(n) for n in range(1, 8)] == [1, 2, 4, 8, 16, 31, 57]
    for rule in (pp.add_more, pp.circle_regions):
        assert [rule(n) for n in (1, 2, 3)] == [1, 2, 4]
    # Circle regions agree with doubling for exactly five items.
    agree = [pp.circle_regions(n) == pp.doubling(n) for n in range(1, 11)]
    assert agree == [True] * 5 + [False] * 5


def test_add_more_rule_adds_one_more_each_time():
    for n in range(1, 40):
        assert pp.add_more(n + 1) - pp.add_more(n) == n
