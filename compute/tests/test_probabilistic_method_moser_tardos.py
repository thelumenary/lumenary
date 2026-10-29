import math
import random

import probabilistic_method_moser_tardos as mt


def instance():
    return mt.build_instance(400, 150, 5, 10, random.Random(2010))


def test_instance_respects_dependency_bound():
    clauses = instance()
    assert len(clauses) == 150
    assert all(len({v for v, _ in c}) == 5 for c in clauses)
    deg = mt.max_dependency_degree(clauses, 400)
    assert deg <= 10
    assert math.e * 2 ** -5 * (deg + 1) <= 1          # the LLL condition


def test_satisfied():
    clause = ((0, True), (1, False))
    assert mt.satisfied(clause, [True, True])
    assert mt.satisfied(clause, [False, False])
    assert not mt.satisfied(clause, [False, True])


def test_moser_tardos_outputs_satisfying_assignments():
    clauses = instance()
    for seed in range(10):
        assignment, steps = mt.moser_tardos(clauses, 400, random.Random(seed))
        assert all(mt.satisfied(c, assignment) for c in clauses)
        assert steps >= 0


def test_mean_resamplings_below_bound():
    clauses = instance()
    deg = mt.max_dependency_degree(clauses, 400)
    steps = [mt.moser_tardos(clauses, 400, random.Random(s))[1]
             for s in range(40)]
    assert sum(steps) / len(steps) <= len(clauses) / deg


def test_naive_successes_counts_correctly():
    # one clause on one variable: half of all assignments satisfy it
    hits = mt.naive_successes([((0, True),)], 1, 4000, random.Random(1))
    assert abs(hits / 4000 - 0.5) < 0.05
    assert mt.naive_successes([((0, True),), ((0, False),)], 1, 100,
                              random.Random(2)) == 0


def test_neighbours():
    clauses = [((0, True), (1, True)), ((1, False), (2, True)),
               ((3, True), (4, True))]
    occ = [set() for _ in range(5)]
    for i, c in enumerate(clauses):
        for v, _ in c:
            occ[v].add(i)
    assert mt.neighbours(clauses, 0, occ) == {1}
    assert mt.neighbours(clauses, 2, occ) == set()
