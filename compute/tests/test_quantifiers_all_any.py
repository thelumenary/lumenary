import quantifiers_all_any as qa


def test_forall_and_exists_on_small_sets():
    assert qa.forall(range(10), lambda n: n < 10)
    assert not qa.forall(range(10), lambda n: n < 9)
    assert qa.exists(range(10), lambda n: n == 7)
    assert not qa.exists(range(10), lambda n: n > 20)


def test_vacuous_truth():
    assert qa.forall([], lambda n: False)
    assert not qa.exists([], lambda n: True)
    assert qa.forall_exists([], range(3), lambda x, y: False)
    assert not qa.exists_forall([1], [], lambda x, y: True)


def test_predicate_count_and_negation_rules():
    for size in range(6):
        agree, total = qa.negation_rules_hold(range(size))
        assert total == 2 ** size
        assert agree == total
    assert sum(1 for _ in qa.predicates(range(3))) == 8


def test_order_of_quantifiers():
    zs = range(-5, 6)
    assert qa.forall_exists(zs, zs, lambda x, y: x + y == 0)
    assert not qa.exists_forall(zs, zs, lambda x, y: x + y == 0)
    # On a finite cut-off of N, 'every x has a bigger y' fails at the top ...
    assert not qa.forall_exists(range(10), range(10), lambda x, y: y > x)
    # ... but it holds if the y's may come from a bigger range.
    assert qa.forall_exists(range(10), range(11), lambda x, y: y > x)
    assert qa.exists_forall(range(10), range(10), lambda x, y: y >= x)


def test_exists_forall_implies_forall_exists_on_examples():
    import itertools
    xs, ys = range(3), range(3)
    for bits in itertools.product([False, True], repeat=9):
        rel = lambda x, y, b=bits: b[3 * x + y]  # noqa: E731
        if qa.exists_forall(xs, ys, rel):
            assert qa.forall_exists(xs, ys, rel)
