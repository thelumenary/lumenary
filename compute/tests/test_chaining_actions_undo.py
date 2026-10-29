from fractions import Fraction
from itertools import product

import chaining_actions_undo as cu


def test_run_and_undo_example():
    chain = ("add 5", "double")
    assert cu.run(chain, 3) == 16
    assert cu.undo_reverse(chain, 16) == 3
    assert cu.undo_same_order(chain, 16) == Fraction(11, 2)


def test_each_undo_undoes():
    for name, (do, undo) in cu.ACTIONS.items():
        for x in cu.STARTS:
            assert undo(do(x)) == x, name


def test_reverse_order_always_works():
    for length in (1, 2, 3):
        for c in product(cu.ACTIONS, repeat=length):
            assert cu.always_back(c, cu.undo_reverse)


def test_counts():
    assert cu.count_successes(2) == (36, 36, 18)
    assert cu.count_successes(3) == (216, 216, 84)


def test_same_order_works_for_commuting_steps():
    assert cu.always_back(("add 3", "subtract 2", "add 5"), cu.undo_same_order)
    assert cu.always_back(("double", "triple"), cu.undo_same_order)
    assert not cu.always_back(("add 3", "double"), cu.undo_same_order)
