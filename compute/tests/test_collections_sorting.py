import pytest

import collections_sorting as cs

ITEMS = [("fig", "fruit", "purple"), ("pea", "vegetable", "green"), ("kiwi", "fruit", "green")]


def test_value_reads_each_property():
    item = ("lime", "fruit", "green")
    assert cs.value(item, "name") == "lime"
    assert cs.value(item, "kind") == "fruit"
    assert cs.value(item, "colour") == "green"


def test_value_rejects_unknown_property():
    with pytest.raises(ValueError):
        cs.value(("lime", "fruit", "green"), "price")


def test_sort_by_is_stable_priority_order_and_does_not_mutate():
    original = list(ITEMS)
    result = cs.sort_by(ITEMS, "colour", "name")
    assert [cs.value(i, "name") for i in result] == ["kiwi", "pea", "fig"]
    assert ITEMS == original


def test_sort_by_without_properties_sorts_tuples():
    assert cs.sort_by(ITEMS) == sorted(ITEMS)


def test_group_by_partitions_items():
    groups = cs.group_by(cs.BASKET, "kind")
    assert list(groups) == ["fruit", "vegetable"]
    assert sum(len(g) for g in groups.values()) == len(cs.BASKET)
    assert all(cs.value(i, "kind") == k for k, g in groups.items() for i in g)


def test_count_by_basket_values():
    assert cs.count_by(cs.BASKET, "kind") == {"fruit": 6, "vegetable": 4}
    assert cs.count_by(cs.BASKET, "colour") == {"brown": 1, "green": 3, "orange": 2, "purple": 1, "yellow": 3}
    assert cs.count_by(cs.BASKET, "name")["mango"] == 2


def test_count_by_empty_collection():
    assert cs.count_by([], "kind") == {}
    assert cs.group_by([], "kind") == {}


def test_counts_are_keyed_in_sorted_order():
    assert list(cs.count_by(cs.BASKET, "colour")) == sorted(cs.count_by(cs.BASKET, "colour"))


def test_distinct_values_counts_names_not_items():
    names = cs.distinct_values(cs.BASKET, "name")
    assert len(cs.BASKET) == 10
    assert len(names) == 8
    assert {"mango", "lime"} <= names


def test_counts_same_in_every_order_checks_all_permutations():
    checked, same = cs.counts_same_in_every_order(cs.BASKET[:6], "kind")
    assert (checked, same) == (720, True)


@pytest.mark.parametrize("n", [0, 1, 2, 3])
def test_counts_same_in_every_order_small_boundaries(n):
    import math
    checked, same = cs.counts_same_in_every_order(cs.BASKET[:n], "colour")
    assert checked == math.factorial(n)
    assert same


def test_format_counts_shows_total():
    assert cs.format_counts({"a": 2, "b": 3}) == "a 2, b 3   (total 5)"
