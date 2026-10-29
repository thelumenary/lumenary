from fractions import Fraction

import model_theory_dlo_qe as qe


def test_eliminate_bounds_only():
    atoms = [("lt", "a", "x"), ("lt", "b", "x"), ("lt", "x", "c")]
    assert qe.eliminate(atoms) == [("lt", "a", "c"), ("lt", "b", "c")]
    # Only lower bounds (or only upper bounds): no endpoints, so always true.
    assert qe.eliminate([("lt", "a", "x")]) == []
    assert qe.eliminate([("lt", "x", "b"), ("lt", "x", "c")]) == []


def test_eliminate_with_equation_substitutes():
    atoms = [("eq", "x", "c"), ("lt", "a", "x"), ("eq", "x", "d")]
    assert qe.eliminate(atoms) == [("eq", "c", "d"), ("lt", "a", "c")]


def test_holds_and_witness_in_q():
    atoms = [("lt", "a", "x"), ("lt", "x", "b")]
    close = {"a": Fraction(1, 3), "b": Fraction(1, 2)}
    assert qe.holds(qe.eliminate(atoms), close)
    assert qe.witness_exists(atoms, close)
    reversed_ = {"a": Fraction(1, 2), "b": Fraction(1, 3)}
    assert not qe.witness_exists(atoms, reversed_)


def test_integers_are_not_dense():
    atoms = [("lt", "a", "x"), ("lt", "x", "b")]
    values = {"a": 0, "b": 1}
    assert qe.holds(qe.eliminate(atoms), values)
    assert not qe.witness_exists(atoms, values, integers=True)


def test_random_agreement_in_q_and_failures_in_z():
    agree, bad = qe.compare(500, seed=7)
    assert agree == 500 and bad == []
    agree_z, bad_z = qe.compare(500, integers=True, seed=7)
    assert bad_z and agree_z + len(bad_z) == 500
    for atoms, values in bad_z:
        # Every failure in Z: the formula is true but no integer witness exists.
        assert qe.holds(qe.eliminate(atoms), values)
        assert not qe.witness_exists(atoms, values, integers=True)


def test_deterministic_output():
    assert qe.compare(100) == qe.compare(100)
    assert qe.show([]) == "true"
