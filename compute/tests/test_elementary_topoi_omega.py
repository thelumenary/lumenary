import itertools
import math

import pytest

import elementary_topoi_omega as et


def test_sieves_on_a_chain_number_k_plus_2():
    elems, leq = et.chain(6)
    assert [len(et.sieves_on(k, elems, leq)) for k in elems] == [2, 3, 4, 5, 6, 7]


def test_down_sets_are_down_closed_and_complete():
    elems, leq = et.POSETS["0 < 2 > 1"]
    ds = et.down_sets(elems, leq)
    assert set(ds) == {frozenset(), frozenset({0}), frozenset({1}),
                       frozenset({0, 1}), frozenset({0, 1, 2})}
    # Discrete poset: every subset is a down-set.
    elems, leq = et.POSETS["discrete 3"]
    assert len(et.down_sets(elems, leq)) == 8


def test_omega1_is_the_three_sieves_on_1():
    assert et.OMEGA1 == [(False, False), (False, True), (True, True)]


@pytest.mark.parametrize("res", [(), (0,), (0, 0, 1), (1, 1, 1, 0), (2, 0, 2)])
def test_counts_match_product_formula(res):
    a1 = len(res)
    a0 = max(res, default=-1) + 1
    fibres = [sum(1 for x in res if x == y) for y in range(a0)]
    expected = math.prod(1 + 2 ** k for k in fibres)
    assert len(et.subpresheaves(a1, a0, res)) == expected
    assert len(et.natural_maps(a1, a0, res)) == expected


def test_chi_is_a_bijection_in_all_small_cases():
    checked, failures = et.check_classifier(3, 3)
    assert checked == 1 + 4 + 15 + 40
    assert failures == []


def test_chi_is_natural_and_recovers_the_subpresheaf():
    a1, a0, res = 3, 2, (0, 0, 1)
    for sub in et.subpresheaves(a1, a0, res):
        f1, f0 = et.chi(sub, a1, a0, res)
        assert all(f1[x][1] == f0[res[x]] for x in range(a1))
        # Pull back "true": (True, True) at stage 1, True at stage 0.
        s1 = frozenset(x for x in range(a1) if f1[x] == (True, True))
        s0 = frozenset(y for y in range(a0) if f0[y])
        assert (s1, s0) == sub


def test_heyting_implication_residuation_on_a_poset():
    elems, leq = et.POSETS["0 < 2 > 1"]
    opens = et.down_sets(elems, leq)
    for u, v, w in itertools.product(opens, repeat=3):
        assert (w <= et.heyting_implies(u, v, opens)) == (w & u <= v)


def test_boolean_exactly_when_discrete():
    assert et.excluded_middle_failures(*et.POSETS["discrete 3"]) == []
    for name in ["{0<1}", "chain of 3", "0 < 2 > 1"]:
        assert et.excluded_middle_failures(*et.POSETS[name]) != []
    # Double negation of every truth value in {0<1} is top: not not (p or not p).
    elems, leq = et.chain(2)
    opens = et.down_sets(elems, leq)
    top, bot = frozenset(elems), frozenset()
    for u in opens:
        lem = u | et.heyting_implies(u, bot, opens)
        nn = et.heyting_implies(et.heyting_implies(lem, bot, opens), bot, opens)
        assert nn == top
