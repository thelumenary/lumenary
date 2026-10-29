from itertools import combinations

import pytest

import kan_extensions_pointwise as kp


def test_colimit_of_discrete_diagram_is_disjoint_union():
    classes = kp.colimit({"a": [0, 1], "b": [0, 1, 2]}, [])
    assert len(classes) == 5
    assert kp.colimit({}, []) == []


def test_colimit_glues_along_maps_and_partitions():
    # A coequaliser of the two maps 0 -> 0 and 0 -> 1 into {0, 1, 2}
    # (written as a diagram x -> y with two arrows) glues 0 and 1 in y.
    sets = {"x": [0], "y": [0, 1, 2]}
    arrows = [("x", "y", lambda v: 0), ("x", "y", lambda v: 1)]
    classes = kp.colimit(sets, arrows)
    assert len(classes) == 2
    union = set().union(*classes)
    assert union == {("x", 0), ("y", 0), ("y", 1), ("y", 2)}
    assert sum(len(c) for c in classes) == len(union)


def test_limit_empty_discrete_and_equaliser():
    assert len(kp.limit({}, [])) == 1
    assert len(kp.limit({"a": [0, 1], "b": [0, 1, 2]}, [])) == 6
    # Equaliser of x -> x mod 2 and x -> 0 on {0..5}: the even numbers.
    sets = {"s": list(range(6)), "t": [0, 1]}
    arrows = [("s", "t", lambda v: v % 2), ("s", "t", lambda v: 0)]
    assert [f["s"] for f in kp.limit(sets, arrows)] == [0, 2, 4]


def test_poset_lan_and_ran_table():
    expected = {"bot": (0, 6), "a": (2, 2), "b": (3, 3), "top": (5, 1)}
    for d, (lan, ran) in expected.items():
        args = (kp.POSET_C, kp.leq_discrete, lambda c: c, kp.leq_d, d,
                kp.POSET_SETS, None)
        assert kp.lan_size(*args) == lan
        assert kp.ran_size(*args) == ran


def test_chain_colimit_and_limit_are_values_at_terminal_and_initial():
    sets, arrows = kp.thin_diagram(kp.CHAIN, lambda x, y: x <= y,
                                   kp.CHAIN_SETS, kp.chain_map)
    assert len(kp.colimit(sets, arrows)) == len(kp.CHAIN_SETS[2])
    assert len(kp.limit(sets, arrows)) == len(kp.CHAIN_SETS[0])


def test_chain_map_is_functorial():
    for x in kp.CHAIN_SETS[0]:
        assert kp.chain_map(0, 2, x) == kp.chain_map(1, 2, kp.chain_map(0, 1, x))
        assert kp.chain_map(0, 0, x) == x


def test_sign_and_compose():
    assert kp.sign((0, 1, 2)) == 1 and kp.sign((1, 0, 2)) == -1
    assert kp.sign((1, 2, 0)) == 1
    for p in kp.S3:
        for q in kp.S3:
            assert kp.sign(kp.compose(p, q)) == kp.sign(p) * kp.sign(q)


def all_subgroups(G):
    ident = (0, 1, 2)
    subs = set()
    for r in range(1, len(G) + 1):
        for cand in combinations(G, r):
            s = set(cand)
            if ident in s and all(kp.compose(p, q) in s for p in s for q in s):
                subs.add(frozenset(s))
    return subs


@pytest.mark.parametrize("size", [1, 2, 3])
def test_induction_and_coinduction_counts_for_every_subgroup(size):
    subs = all_subgroups(kp.S3)
    assert len(subs) == 6  # 1, three of order 2, A3, S3
    X = list(range(size))
    for H in subs:
        H = sorted(H)
        index = len(kp.S3) // len(H)
        trivial = lambda h, x: x  # noqa: E731
        lan = kp.colimit(*kp.induced_diagram(kp.S3, H, X, trivial))
        ran = kp.limit(*kp.coinduced_diagram(kp.S3, H, X, trivial))
        assert len(lan) == index * size
        assert len(ran) == size ** index


def test_nontrivial_actions_in_report():
    for name, H, X, act in kp.subgroup_cases():
        index = len(kp.S3) // len(H)
        assert len(kp.colimit(*kp.induced_diagram(kp.S3, H, X, act))) == index * len(X)
        assert len(kp.limit(*kp.coinduced_diagram(kp.S3, H, X, act))) == len(X) ** index
