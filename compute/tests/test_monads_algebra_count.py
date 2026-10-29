import math

import monads_algebra_count as mac


def test_maybe_algebras_are_base_points():
    for n in range(5):
        algebras = mac.maybe_algebras(n)
        assert len(algebras) == n
        # Each algebra is the identity on X and sends None (index n) anywhere.
        assert sorted(a[n] for a in algebras) == list(range(n))
        assert all(a[:n] == tuple(range(n)) for a in algebras)


def test_powerset_algebra_counts_match_labelled_chains():
    # Complete lattices on at most 3 points are chains: n! labellings.
    for n in range(1, 4):
        algebras = mac.powerset_algebras(n)
        assert len(algebras) == math.factorial(n)
        for act in algebras:
            rel = mac.order_of(act, n)
            assert mac.is_chain(rel, n)
            assert mac.is_least_upper_bound_map(act, rel, n)


def test_max_is_an_algebra_but_empty_set_must_go_to_bottom():
    n = 3
    act_max = {m: (max(mac.members(m)) if m else 0) for m in mac.subsets(n)}
    assert mac.is_powerset_algebra(act_max, n)
    # Sending the empty set to the top element breaks associativity: for the
    # family {empty, {0}}, a({a(empty), a({0})}) = a({2, 0}) = 2, while
    # a(union) = a({0}) = 0.
    act_bad = dict(act_max)
    act_bad[0] = 2
    assert not mac.is_powerset_algebra(act_bad, n)


def test_members_and_subsets():
    assert mac.members(0) == []
    assert mac.members(0b101) == [0, 2]
    assert len(mac.subsets(3)) == 8


def test_list_algebra_law_detects_non_associativity():
    magmas = mac.unital_magmas(2)
    # Unital operations on 2 points: choose the unit, then x * x.
    assert len(magmas) == 4
    for rows, unit in magmas:
        assert mac.is_associative(rows, 2)
        assert mac.list_algebra_law_holds(rows, unit, 2)
    # A unital but non-associative operation on 3 points.
    rows = ((0, 1, 2), (1, 2, 0), (2, 1, 0))
    assert not mac.is_associative(rows, 3)
    assert not mac.list_algebra_law_holds(rows, 0, 3)


def test_list_algebras_on_three_points_are_exactly_monoids():
    magmas = mac.unital_magmas(3)
    assert len(magmas) == 243
    algebra = [m for m in magmas if mac.list_algebra_law_holds(*m, 3)]
    assoc = [m for m in magmas if mac.is_associative(m[0], 3)]
    assert algebra == assoc
    assert len(assoc) == 33


def test_fold_is_right_fold_with_unit():
    rows = ((0, 1, 2), (1, 2, 0), (2, 0, 1))  # addition mod 3, unit 0
    assert mac.fold(rows, 0, []) == 0
    assert mac.fold(rows, 0, [1, 1, 2, 2]) == 0
    assert mac.fold(rows, 0, [2, 2]) == 1


def test_intersection_breaks_unit_law():
    mask, meet = mac.intersection_unit_counterexample(3)
    assert mac.members(mask) == [0, 1]
    assert meet == 0
