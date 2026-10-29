from math import comb

import pytest

import descriptive_set_theory_trees as dt


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def test_trees_are_prefix_closed_and_pruned():
    for _, tree in dt.TREES:
        for n in range(8):
            for t in dt.level(tree, n):
                assert all(tree(t[:k]) for k in range(len(t)))
                assert tree(t + "0")  # every node extends: the tree is pruned


def test_level_counts():
    for n in range(12):
        assert len(dt.level(dt.full, n)) == 2 ** n
        assert len(dt.level(dt.golden, n)) == fib(n + 2)
        assert len(dt.level(dt.at_most_two, n)) == 1 + n + comb(n, 2)
        assert len(dt.level(dt.staircase, n)) == fib(n + 2)


def test_splitting_heights():
    for n in range(1, 13):
        assert dt.splitting_height(dt.full, n) == n
        assert dt.splitting_height(dt.golden, n) == (n + 1) // 2
        assert dt.splitting_height(dt.at_most_two, n) == min(n, 2)
    # Above the node "1" the staircase tree has a single branch 1000...
    assert dt.splitting_height(dt.staircase, 10, "1") == 0
    with pytest.raises(ValueError):
        dt.splitting_height(dt.golden, 5, "11")


def test_finite_perfectness_test():
    assert dt.every_node_branches(dt.full, 8)
    assert dt.every_node_branches(dt.golden, 10)
    assert not dt.every_node_branches(dt.at_most_two, 8)
    assert not dt.every_node_branches(dt.staircase, 8)
