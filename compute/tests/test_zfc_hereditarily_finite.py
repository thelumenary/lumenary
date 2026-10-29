import pytest

import zfc_hereditarily_finite as hf

E = hf.EMPTY


def test_hierarchy_sizes_are_iterated_powers_of_two():
    stages = hf.hierarchy(4)
    assert [len(v) for v in stages] == [0, 1, 2, 4, 16]
    # Each stage is contained in the next (the hierarchy is cumulative).
    assert all(a <= b for a, b in zip(stages, stages[1:]))
    with pytest.raises(ValueError):
        hf.hierarchy(-1)


def test_numerals_are_transitive_and_have_n_elements():
    for n in range(6):
        x = hf.numeral(n)
        assert len(x) == n
        assert all(y <= x for y in x), "every element is a subset (transitivity)"
        assert set(x) == {hf.numeral(m) for m in range(n)}
    assert hf.numeral(0) == E
    with pytest.raises(ValueError):
        hf.numeral(-2)


def test_kuratowski_pairs_never_collide_on_v4():
    v4 = hf.hierarchy(4)[4]
    assert hf.collisions(v4, hf.kpair) == []
    # Degenerate pair (a, a) is the singleton {{a}}.
    a = hf.numeral(1)
    assert hf.kpair(a, a) == frozenset([frozenset([a])])


def test_naive_pairs_collide():
    v4 = hf.hierarchy(4)[4]
    bad = hf.collisions(v4, hf.naive_pair)
    assert bad
    for (a, b), (c, d) in bad:
        assert (a, b) != (c, d)
        assert hf.naive_pair(a, b) == hf.naive_pair(c, d)


def test_foundation_holds_for_hereditarily_finite_sets():
    v4 = hf.hierarchy(4)[4]
    assert all(hf.has_minimal_element(x) for x in v4 if x)
    assert not hf.has_minimal_element(E)


def test_ackermann_coding_is_a_bijection_respecting_membership():
    for n in range(64):
        assert hf.ackermann(hf.decode(n)) == n
    v4 = hf.hierarchy(4)[4]
    assert sorted(hf.ackermann(x) for x in v4) == list(range(16))
    assert [hf.ackermann(hf.numeral(n)) for n in range(5)] == [0, 1, 3, 11, 2059]
    for x in v4:
        for y in v4:
            assert (x in y) == bool(hf.ackermann(y) >> hf.ackermann(x) & 1)
    with pytest.raises(ValueError):
        hf.decode(-1)


def test_powerset_and_show():
    s = frozenset([E, hf.numeral(1)])
    assert len(hf.powerset(s)) == 4
    assert hf.show(hf.numeral(2)) == "{{}, {{}}}"
    assert hf.succ(E) == frozenset([E])
