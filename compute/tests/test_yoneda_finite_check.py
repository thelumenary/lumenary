import pytest

import yoneda_finite_check as yc


@pytest.mark.parametrize("example", yc.examples(), ids=lambda e: e[0])
def test_yoneda_count_and_bijection(example):
    _, cat, a, obj, arr = example
    n_nat, size, candidates, bijective = yc.yoneda_check(cat, a, obj, arr)
    assert n_nat == size
    assert bijective
    assert candidates >= n_nat


def test_hom_sets_of_parallel_pair():
    pp = yc.parallel_pair()
    assert sorted(pp.hom("E", "V")) == ["s", "t"]
    assert pp.hom("V", "E") == []
    assert pp.hom("E", "E") == ["1E"]


def test_t2_is_a_monoid():
    one = (0, 1)
    for f in yc.T2:
        assert yc.t2_mul(one, f) == f == yc.t2_mul(f, one)
        for g in yc.T2:
            assert yc.t2_mul(g, f) in yc.T2
            for h in yc.T2:
                assert yc.t2_mul(h, yc.t2_mul(g, f)) == yc.t2_mul(yc.t2_mul(h, g), f)


def test_non_natural_families_are_rejected():
    # For a graph with one edge a -> b, the family sending the edge to itself
    # but s to b (wrong endpoint) must not count as natural.
    pp = yc.parallel_pair()
    obj = {"E": ["e"], "V": ["a", "b"]}
    arr = {"1E": {"e": "e"}, "1V": {"a": "a", "b": "b"},
           "s": {"e": "a"}, "t": {"e": "b"}}
    nats, candidates = yc.natural_transformations(pp, "E", obj, arr)
    assert candidates == 4
    assert nats == [{"1E": "e", "s": "a", "t": "b"}]


def test_cayley():
    count, exact = yc.cayley_check()
    assert count == 6 and exact


def test_divisibility_yoneda():
    pairs, failures = yc.divisibility_check(30)
    assert pairs == 900 and failures == 0
