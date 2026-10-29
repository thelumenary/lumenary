import equivalence_relations_count as erc


def test_property_checks_on_examples():
    eq = frozenset({(0, 0), (1, 1), (2, 2), (0, 1), (1, 0)})
    assert erc.is_equivalence(3, eq)
    less = frozenset({(0, 1), (0, 2), (1, 2)})
    assert not erc.is_reflexive(3, less)
    assert not erc.is_symmetric(less)
    assert erc.is_transitive(less)
    near = frozenset({(a, b) for a in range(3) for b in range(3) if abs(a - b) <= 1})
    assert erc.is_reflexive(3, near) and erc.is_symmetric(near)
    assert not erc.is_transitive(near)  # (0, 1) and (1, 2) but not (0, 2)


def test_empty_relation_is_symmetric_and_transitive_but_not_reflexive():
    empty = frozenset()
    assert erc.is_symmetric(empty) and erc.is_transitive(empty)
    assert not erc.is_reflexive(1, empty)
    assert erc.is_reflexive(0, empty)  # vacuously reflexive on the empty set


def test_relation_counts_on_three_elements():
    c = erc.property_counts(3)
    assert c == {"all": 512, "refl": 64, "symm": 64, "trans": 171, "equiv": 5}
    assert erc.property_counts(2) == {"all": 16, "refl": 4, "symm": 8, "trans": 13, "equiv": 2}


def test_generators_have_the_right_sizes():
    assert sum(1 for _ in erc.all_relations(2)) == 16
    assert sum(1 for _ in erc.symmetric_relations(3)) == 2 ** 6
    assert all(erc.is_symmetric(r) for r in erc.symmetric_relations(3))
    assert len(set(erc.symmetric_relations(3))) == 64


def test_set_partitions_and_bell_numbers():
    assert erc.bell_numbers(7) == [1, 1, 2, 5, 15, 52, 203]
    for n in range(0, 6):
        parts = list(erc.set_partitions(n))
        assert len(parts) == len(set(parts)) == erc.bell_numbers(n + 1)[n]
        for p in parts:
            assert all(p)  # blocks are non-empty
            assert sorted(x for block in p for x in block) == list(range(n))


def test_classes_of_an_equivalence_form_its_partition():
    eq = frozenset({(0, 0), (1, 1), (2, 2), (3, 3), (0, 2), (2, 0)})
    assert erc.classes(4, eq) == frozenset({frozenset({0, 2}), frozenset({1}), frozenset({3})})


def test_bijection_between_equivalences_and_partitions():
    expected = {1: (1, 1, True, 2), 2: (2, 2, True, 5), 3: (5, 5, True, 15), 4: (15, 15, True, 52)}
    for n, result in expected.items():
        assert erc.compare(n) == result
