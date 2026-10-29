from fractions import Fraction

import fractions_adding_rules as far


def test_add_rule_values():
    assert far.add_rule(1, 2, 1, 3) == (5, 6)
    assert far.add_rule(3, 4, 1, 6) == (22, 24)
    assert Fraction(*far.add_rule(3, 4, 1, 6)) == Fraction(11, 12)
    assert far.add_rule(0, 5, 2, 7) == (10, 35)


def test_wrong_rule_is_the_mediant_and_is_not_the_sum():
    assert far.wrong_rule(1, 2, 1, 3) == (2, 5)
    assert Fraction(2, 5) < Fraction(1, 2) < Fraction(5, 6)
    # For positive fractions the wrong rule never gives the sum.
    for a, b in far.fractions_in_unit_interval(6):
        for c, d in far.fractions_in_unit_interval(6):
            assert Fraction(*far.wrong_rule(a, b, c, d)) != Fraction(a, b) + Fraction(c, d)


def test_equivalent_matches_exact_equality():
    assert far.equivalent(2, 4, 1, 2)
    assert far.equivalent(6, 8, 3, 4)
    assert not far.equivalent(2, 3, 3, 4)
    assert far.equivalent(0, 5, 0, 9)
    pairs, agree, equal = far.cross_test_agrees(6, 6)
    assert pairs == agree == 42 * 42
    assert equal > 42


def test_compare_rules_small_case():
    fracs = far.fractions_in_unit_interval(3)
    assert fracs == [(1, 1), (1, 2), (2, 2), (1, 3), (2, 3), (3, 3)]
    pairs, right, wrong, between = far.compare_rules(3)
    assert pairs == right == between == 36
    assert wrong == 0


def test_floats_differ_from_fractions():
    assert 0.1 + 0.2 != 0.3
    assert Fraction(1, 10) + Fraction(2, 10) == Fraction(3, 10)
