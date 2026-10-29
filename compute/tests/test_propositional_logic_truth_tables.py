from itertools import product

import pytest

import propositional_logic_truth_tables as pl


def test_rows_textbook_order_and_count():
    assert pl.rows(0) == [()]
    assert pl.rows(2) == [(True, True), (True, False), (False, True), (False, False)]
    for n in range(6):
        assert len(pl.rows(n)) == 2 ** n
    with pytest.raises(ValueError):
        pl.rows(-1)


def test_conditional_truth_table():
    # p -> q is false only in the row p = T, q = F.
    assert pl.table(pl.implies, 2) == (True, False, True, True)


def test_contrapositive_equivalent_converse_not():
    cond = pl.implies
    contra = lambda p, q: pl.implies(not q, not p)
    converse = lambda p, q: pl.implies(q, p)
    inverse = lambda p, q: pl.implies(not p, not q)
    assert pl.differing_rows(cond, contra, 2) == []
    assert pl.differing_rows(cond, converse, 2) == [(True, False), (False, True)]
    # The converse and the inverse are contrapositives of each other.
    assert pl.differing_rows(converse, inverse, 2) == []


def test_classify():
    assert pl.classify(lambda p: p or not p, 1) == "tautology"
    assert pl.classify(lambda p: p and not p, 1) == "contradiction"
    assert pl.classify(lambda p, q: p and q, 2) == "contingent"
    modus_ponens = lambda p, q: pl.implies(pl.implies(p, q) and p, q)
    affirming = lambda p, q: pl.implies(pl.implies(p, q) and q, p)
    assert pl.classify(modus_ponens, 2) == "tautology"
    assert pl.classify(affirming, 2) == "contingent"


def test_de_morgan_three_variables():
    f = lambda p, q, r: (not (p and q and r)) == ((not p) or (not q) or (not r))
    assert pl.classify(f, 3) == "tautology"


@pytest.mark.parametrize("values", list(product([True, False], repeat=4)))
def test_dnf_and_nand_rebuild_every_table(values):
    text = pl.dnf_from_table(values)
    rebuilt = pl.table(lambda p, q: pl.evaluate_dnf(text, {"p": p, "q": q}), 2)
    assert rebuilt == values
    assert pl.table(pl.nand_only(values), 2) == values


def test_dnf_examples():
    assert pl.dnf_from_table((False, True, True, False)) == "(p and not q) or (not p and q)"
    assert pl.dnf_from_table((False,) * 4) == "(p and not p)"
    three = pl.dnf_from_table((True,) + (False,) * 7, names=("p", "q", "r"))
    assert three == "(p and q and r)"
