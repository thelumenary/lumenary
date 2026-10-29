import equivalence_relations_checker as erc


def test_counterexamples_for_less_than():
    xs = list(range(4))
    lt = lambda a, b: a < b  # noqa: E731
    assert erc.reflexive_counterexample(xs, lt) == (0,)
    assert erc.symmetric_counterexample(xs, lt) == (0, 1)
    assert erc.transitive_counterexample(xs, lt) is None


def test_differ_by_at_most_one_is_not_transitive():
    xs = list(range(6))
    near = lambda a, b: abs(a - b) <= 1  # noqa: E731
    assert erc.reflexive_counterexample(xs, near) is None
    assert erc.symmetric_counterexample(xs, near) is None
    a, b, c = erc.transitive_counterexample(xs, near)
    assert near(a, b) and near(b, c) and not near(a, c)


def test_classes_of_same_remainder():
    xs = list(range(12))
    blocks = erc.equivalence_classes(xs, lambda a, b: a % 3 == b % 3)
    assert blocks == [[0, 3, 6, 9], [1, 4, 7, 10], [2, 5, 8, 11]]
    assert erc.is_partition(xs, blocks)


def test_is_partition_rejects_overlaps_gaps_and_empty_blocks():
    xs = [1, 2, 3]
    assert erc.is_partition(xs, [[1], [2, 3]])
    assert not erc.is_partition(xs, [[1, 2], [2, 3]])  # overlap
    assert not erc.is_partition(xs, [[1], [2]])  # 3 is missing
    assert not erc.is_partition(xs, [[1, 2, 3], []])  # empty block


def test_country_relations():
    countries = erc.COUNTRIES
    blocks = erc.equivalence_classes(countries, erc.same_letters_count)
    assert erc.is_partition(countries, blocks)
    assert sorted(len(b[0]) for b in blocks) == [4, 5, 6]
    a, b, c = erc.transitive_counterexample(countries, erc.share_a_letter)
    assert erc.share_a_letter(a, b) and erc.share_a_letter(b, c)
    assert not erc.share_a_letter(a, c)


def test_report_lines():
    lines = erc.report("divides", list(range(1, 7)), lambda a, b: b % a == 0)
    assert lines[0] == "divides: reflexive, not symmetric, transitive"
    assert lines[1] == "   fails symmetric: (1, 2)"
    eq_lines = erc.report("parity", list(range(4)), lambda a, b: a % 2 == b % 2)
    assert eq_lines[1] == "   2 classes: {0,2} {1,3}"
