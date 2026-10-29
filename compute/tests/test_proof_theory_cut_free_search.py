from itertools import product

import proof_theory_cut_free_search as pt


def all_valuations(n):
    for bits in product([False, True], repeat=n):
        yield dict(enumerate(bits))


def is_tautology(goal, n):
    return all(any(pt.evaluate(f, v) for f in goal) for v in all_valuations(n))


def test_dual_is_negation_and_involution():
    f = pt.Or(pt.And(pt.P(0), pt.N(1)), pt.P(2))
    assert pt.dual(pt.dual(f)) == f
    for v in all_valuations(3):
        assert pt.evaluate(pt.dual(f), v) == (not pt.evaluate(f, v))


def test_search_agrees_with_truth_tables():
    # Completeness and soundness of the cut-free calculus on every example.
    for _, goal in pt.EXAMPLES:
        kind, _ = pt.search(goal)
        assert (kind == "proof") == is_tautology(goal, 3)


def test_exhaustive_small_formulas():
    atoms = [pt.P(0), pt.N(0), pt.P(1), pt.N(1)]
    formulas = list(atoms)
    for a, b in product(atoms, repeat=2):
        formulas += [pt.And(a, b), pt.Or(a, b)]
    for f, g in product(formulas, repeat=2):
        goal = [f, g]
        for strategy in ("leftmost", "guided"):
            kind, result = pt.search(goal, strategy)
            assert (kind == "proof") == is_tautology(goal, 2)
            if kind == "countermodel":
                v = {0: False, 1: False, **result}
                assert not any(pt.evaluate(h, v) for h in goal)


def test_subformula_property_of_found_proofs():
    for _, goal in pt.EXAMPLES[:-1]:
        kind, tree = pt.search(goal)
        assert kind == "proof"
        assert pt.has_subformula_property(tree, goal)
    bogus = ("axiom", (pt.P(5), pt.N(5)), ())
    assert not pt.has_subformula_property(bogus, [pt.P(0)])


def test_identity_proof_sizes():
    sizes = []
    for n in range(1, 7):
        a = pt.disjunction([pt.And(pt.P(2 * i), pt.P(2 * i + 1)) for i in range(n)])
        left = pt.size(pt.search([pt.dual(a), a], "leftmost")[1])
        guided = pt.size(pt.search([pt.dual(a), a], "guided")[1])
        assert guided == 6 * n - 2
        sizes.append(left)
    # The leftmost order grows exponentially: each step more than doubles.
    assert all(b > 2 * a for a, b in zip(sizes[1:], sizes[2:]))


def test_size_and_depth_of_excluded_middle():
    kind, tree = pt.search([pt.Or(pt.P(0), pt.N(0))])
    assert kind == "proof" and pt.size(tree) == 2 and pt.depth(tree) == 2
    assert pt.show(pt.Or(pt.P(0), pt.N(0))) == "(p0 | ~p0)"
