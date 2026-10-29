import pytest
import sympy

import variables_expressions_equivalence as ve

a, b, n, x = ve.a, ve.b, ve.n, ve.x


def test_ordered_values_small_first():
    assert ve.ordered_values(0) == [0]
    assert ve.ordered_values(3) == [0, 1, -1, 2, -2, 3, -3]
    assert sorted(ve.ordered_values(5)) == list(range(-5, 6))
    with pytest.raises(ValueError):
        ve.ordered_values(-1)


def test_assignments_cover_the_grid():
    grid = ve.assignments({a, b}, 2)
    assert len(grid) == 25
    assert {(d[a], d[b]) for d in grid} == {(p, q) for p in range(-2, 3) for q in range(-2, 3)}
    assert ve.assignments(set(), 4) == [{}]


def test_equivalent_pairs_pass_and_false_ones_fail():
    results = {name: ve.first_counterexample(lhs, rhs, 3) for name, lhs, rhs in ve.PAIRS}
    assert results["4 + 3(n - 1)  vs  3n + 1"] == (7, None)
    assert results["(a + b)^2  vs  a^2 + 2ab + b^2"] == (49, None)
    tests, bad = results["(a + b)^2  vs  a^2 + b^2"]
    assert bad == {a: 1, b: 1} and tests == 9
    tests, bad = results["2x  vs  x^2"]
    assert bad == {x: 1} and tests == 2


def test_trap_agrees_on_four_values_then_differs():
    lhs, rhs = ve.TRAP
    assert [ve.value(lhs, {x: k}) == ve.value(rhs, {x: k}) for k in range(6)] == [True] * 4 + [False] * 2
    assert ve.value(lhs, {x: 4}) == 28
    # Restricting the tests to 0..3 would never catch it; -1 does.
    assert ve.value(lhs, {x: -1}) == -1 + 24


def test_agreement_count_matches_theorem():
    # (a + b)^2 = a^2 + b^2 exactly when a = 0 or b = 0: 2(2r + 1) - 1 points.
    for r in (0, 1, 5, 20):
        hits, total = ve.agreement_count(r)
        assert total == (2 * r + 1) ** 2
        assert hits == 2 * (2 * r + 1) - 1


def test_symbolic_differences():
    assert ve.symbolic_difference(4 + 3 * (n - 1), 3 * n + 1) == 0
    assert ve.symbolic_difference((a + b) ** 2, a ** 2 + b ** 2) == 2 * a * b
    lhs, rhs = ve.TRAP
    assert sympy.factor(ve.symbolic_difference(lhs, rhs)) == x * (x - 1) * (x - 2) * (x - 3)


def test_describe_is_readable():
    assert ve.describe({b: -3, a: 2}) == "a = 2, b = -3"
