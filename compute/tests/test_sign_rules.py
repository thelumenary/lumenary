import pytest
import sympy

import sign_rules as sr


def test_grid_size_and_bounds():
    assert sr.grid(0) == [(0, 0)]
    pairs = sr.grid(10)
    assert len(pairs) == 441
    assert (-10, 10) in pairs and (10, -10) in pairs and (11, 0) not in pairs
    with pytest.raises(ValueError):
        sr.grid(-1)


@pytest.mark.parametrize("rule", [sr.neg_times_neg, sr.neg_times_pos])
def test_rules_hold_on_grid(rule):
    cases, failures = sr.check_on_grid(rule, sr.grid(10))
    assert cases == 441
    assert failures == []


def test_rules_hold_for_large_and_rational_values():
    from fractions import Fraction
    for a, b in [(10**30, -(10**25)), (Fraction(-3, 7), Fraction(5, 2)), (0, -5)]:
        assert sr.neg_times_neg(a, b)
        assert sr.neg_times_pos(a, b)


def test_check_on_grid_reports_failures():
    cases, failures = sr.check_on_grid(lambda a, b: (-a) * (-b) == -(a * b), sr.grid(1))
    assert cases == 9
    # The false rule only "holds" when a*b == 0.
    assert set(failures) == {(-1, -1), (-1, 1), (1, -1), (1, 1)}


def test_symbolic_difference():
    a, b = sympy.symbols("a b")
    assert sr.symbolic_difference((-a) * (-b), a * b) == 0
    assert sr.symbolic_difference((-a) * b, -(a * b)) == 0
    assert sr.symbolic_difference((a + b) ** 2, a ** 2 + b ** 2) == 2 * a * b


def test_symbolic_examples_values():
    a, b = sympy.symbols("a b")
    rows = dict(sr.symbolic_examples())
    assert rows["(-a)*(-b)"] == a * b
    assert rows["(-a)*(-b) - a*b, expanded"] == 0
    assert rows["(-a)*b + a*b, expanded"] == 0
    assert rows["(a - b)*(a + b), expanded"] == a ** 2 - b ** 2
    assert rows["how SymPy stores -a"] == "Mul(Integer(-1), Symbol('a'))"


def test_sign_rule_without_commutativity():
    A, B = sympy.symbols("A B", commutative=False)
    rows = dict(sr.symbolic_examples())
    assert rows["(-A)*(-B), non-commuting A, B"] == A * B
    assert rows["A*B - B*A, non-commuting A, B"] != 0


def test_proof_steps_are_listed_in_order():
    steps = [s for s, _ in sr.PROOF_STEPS]
    assert steps[0].startswith("0 =")
    assert steps[-1] == "so (-a)(-b) = ab"
    assert any("distributive" in reason for _, reason in sr.PROOF_STEPS)
