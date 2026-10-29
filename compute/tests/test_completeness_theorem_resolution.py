import random

import completeness_theorem_resolution as cr

F = frozenset


def test_resolvents():
    assert cr.resolvents(F([1, 2]), F([-1, 3])) == [F([2, 3])]
    assert cr.resolvents(F([1]), F([-1])) == [F()]
    # Resolving on 1 would leave the tautology {2, -2}: discarded.
    assert cr.resolvents(F([1, 2]), F([-1, -2])) == []
    assert cr.resolvents(F([1, 2]), F([3])) == []


def test_small_refutations_and_non_refutations():
    four = [F(c) for c in ([1, 2], [1, -2], [-1, 2], [-1, -2])]
    assert cr.refutable(four)
    assert not cr.refutable(four[:3])
    assert cr.refutable([F()])
    assert not cr.refutable([])
    assert not cr.satisfiable(four, 2) and cr.satisfiable(four[:3], 2)


def test_soundness_and_completeness_on_random_sets():
    rng = random.Random(5)
    for _ in range(60):
        clauses = cr.random_clauses(rng, 4, rng.randint(6, 20))
        assert cr.refutable(clauses) == (not cr.satisfiable(clauses, 4))


def test_lindenbaum_model_satisfies_consistent_sets():
    rng = random.Random(8)
    checked = 0
    for _ in range(60):
        clauses = cr.random_clauses(rng, 4, rng.randint(4, 12))
        if not cr.refutable(clauses):
            model = cr.lindenbaum_model(clauses, 4)
            assert set(model) == {1, 2, 3, 4}
            assert cr.satisfies(model, clauses)
            checked += 1
    assert checked > 20


def test_random_clauses_shape():
    rng = random.Random(1)
    clauses = cr.random_clauses(rng, 5, 10)
    assert len(clauses) == 10
    for c in clauses:
        assert len(c) == 3 and len({abs(x) for x in c}) == 3
        assert all(1 <= abs(x) <= 5 for x in c)
