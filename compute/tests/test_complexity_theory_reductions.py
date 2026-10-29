import itertools
import random

import complexity_theory_reductions as cr


def test_unsat_core_is_unsatisfiable():
    core = cr.unsat_core(1, 2, 3)
    assert len(core) == 8
    assert cr.satisfying_assignment(core, 3) is None


def test_reduction_graph_shape():
    formula = [(1, 2, -3), (-1, 3, 4), (-2, -4, 3)]
    vertices, masks = cr.reduction_graph(formula)
    assert len(vertices) == 9
    edges = sum(bin(x).count("1") for x in masks) // 2
    assert edges == 9 + 5  # three triangles and five complementary pairs
    # symmetric adjacency, no loops
    for p, q in itertools.product(range(9), repeat=2):
        assert (masks[p] >> q & 1) == (masks[q] >> p & 1)
        assert not (p == q and masks[p] >> q & 1)


def test_independent_set_search_on_small_graphs():
    # 5-cycle: maximum independent set has size 2
    masks = [0] * 5
    for i in range(5):
        j = (i + 1) % 5
        masks[i] |= 1 << j
        masks[j] |= 1 << i
    found = cr.independent_set(masks, 2)
    assert found is not None and cr.is_independent(masks, found)
    assert cr.independent_set(masks, 3) is None


def test_certificates_translate_both_ways():
    rng = random.Random(5)
    for _ in range(40):
        formula = cr.random_3cnf(4, rng.randint(3, 8), rng)
        a = cr.satisfying_assignment(formula, 4)
        _, masks = cr.reduction_graph(formula)
        if a is None:
            assert cr.independent_set(masks, len(formula)) is None
            continue
        picks = cr.assignment_to_set(formula, a)
        assert len(picks) == len(formula) and cr.is_independent(masks, picks)
        found = cr.independent_set(masks, len(formula))
        assert cr.satisfies(formula, cr.set_to_assignment(formula, found, 4))


def test_reduction_agrees_on_all_trial_formulas():
    formulas = cr.trial_formulas()
    assert len(formulas) == 200
    outcomes = set()
    for formula in formulas:
        sat = cr.satisfying_assignment(formula, 4) is not None
        _, masks = cr.reduction_graph(formula)
        indep = cr.independent_set(masks, len(formula)) is not None
        assert sat == indep
        outcomes.add(sat)
    assert outcomes == {True, False}  # both answers occur
