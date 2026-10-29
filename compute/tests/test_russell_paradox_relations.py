import russell_paradox_relations as rp


def test_number_of_relations():
    for n in range(4):
        assert sum(1 for _ in rp.relations(n)) == 2 ** (n * n)


def test_russell_and_member_sets():
    rel = frozenset({(0, 0), (1, 0), (2, 1)})
    assert rp.russell_set(rel, 3) == frozenset({1, 2})
    assert rp.members(rel, 0, 3) == frozenset({0, 1})
    assert rp.members(rel, 1, 3) == frozenset({2})
    assert rp.russell_witnesses(rel, 3) == []


def test_no_russell_witness_ever():
    for n in range(1, 4):
        count, found = rp.search(n)
        assert count == 2 ** (n * n)
        assert found == 0


def test_witness_fails_at_itself():
    # For every relation and every r, r itself is where members(r) and the
    # Russell set disagree.
    for rel in rp.relations(3):
        target = rp.russell_set(rel, 3)
        for r in range(3):
            assert (r in rp.members(rel, r, 3)) != (r in target)


def test_hereditarily_finite_levels():
    v = rp.hereditarily_finite(4)
    assert [len(level) for level in v] == [0, 1, 2, 4, 16]
    assert v[1] == frozenset({frozenset()})
    assert rp.id_of(frozenset({frozenset()})) == "{{}}"
    for a in v[4]:
        assert a not in a
        assert rp.separated_russell(a) == a
        assert rp.separated_russell(a) not in a
