import pytest

import addition_subtraction_facts as asf


def test_fact_table_size_and_turn_around():
    table = asf.facts()
    assert len(table) == 121
    assert (8, 5, 13) in table and (10, 10, 20) in table
    assert all(s == a + b for a, b, s in table)
    assert len(asf.facts_to_learn()) == 66
    assert len(asf.facts_to_learn(0)) == 1
    assert len(asf.facts_to_learn(2)) == 6


def test_take_away_undoes_adding_and_does_not_turn_around():
    for a, b, s in asf.facts():
        assert asf.take_away(s, b) == a
        assert asf.take_away(s, a) == b
    assert asf.take_away(5, 3) == 2
    assert asf.take_away(3, 5) is None
    assert asf.take_away(4, 4) == 0
    both = [(a, b) for a in range(11) for b in range(11)
            if asf.take_away(a, b) is not None and asf.take_away(b, a) is not None]
    assert both == [(a, a) for a in range(11)]


def test_tens_ones_is_unique_and_checked():
    assert asf.tens_ones(52) == (5, 2)
    assert asf.tens_ones(7) == (0, 7)
    assert asf.tens_ones(90) == (9, 0)
    assert sorted(10 * t + o for t in range(10) for o in range(10)) == list(range(100))
    with pytest.raises(ValueError):
        asf.tens_ones(100)
    with pytest.raises(ValueError):
        asf.tens_ones(-1)


def test_place_value_comparison_matches_less_than():
    assert asf.less_by_place_value(47, 52)
    assert not asf.less_by_place_value(52, 47)
    assert asf.less_by_place_value(63, 68)
    assert not asf.less_by_place_value(25, 25)
    assert all(asf.less_by_place_value(a, b) == (a < b) for a in range(100) for b in range(100))


def test_column_addition():
    assert asf.column_add(38, 25) == (63, True)
    assert asf.column_add(32, 45) == (77, False)
    assert asf.column_add(0, 0) == (0, False)
    assert asf.column_add(99, 0) == (99, False)
    with pytest.raises(ValueError):
        asf.column_add(60, 45)
    for a in range(100):
        for b in range(100 - a):
            total, regrouped = asf.column_add(a, b)
            assert total == a + b
            assert regrouped == (a % 10 + b % 10 >= 10)


def test_column_subtraction_and_matching_regroups():
    assert asf.column_subtract(52, 27) == (25, True)
    assert asf.column_subtract(58, 23) == (35, False)
    assert asf.column_subtract(40, 1) == (39, True)
    with pytest.raises(ValueError):
        asf.column_subtract(27, 52)
    for a in range(100):
        for b in range(100 - a):
            # Taking b away from a + b regroups exactly when adding b to a did.
            assert asf.column_subtract(a + b, b) == (a, asf.column_add(a, b)[1])
