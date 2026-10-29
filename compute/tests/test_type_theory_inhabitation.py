import pytest

import type_theory_inhabitation as ti

P = ti.parse


def test_parser_precedence_and_associativity():
    p, q, r = ("atom", "p"), ("atom", "q"), ("atom", "r")
    assert P("p -> q -> r") == ("imp", p, ("imp", q, r))
    assert P("p & q | r") == ("or", ("and", p, q), r)
    assert P("~p") == ("imp", p, ti.BOT)
    assert P("~~p -> p") == ("imp", ("imp", ("imp", p, ti.BOT), ti.BOT), p)
    with pytest.raises(ValueError):
        P("(p -> q")


@pytest.mark.parametrize("src", [
    "p -> p", "p -> q -> p", "(p -> q -> r) -> (p -> q) -> p -> r",
    "p -> ~~p", "~~~p -> ~p", "~~(p | ~p)", "~(p | q) -> ~p & ~q",
    "(p -> q) -> ~q -> ~p", "~~(((p -> q) -> p) -> p)", "p & q -> q & p",
    "p | q -> q | p", "(p -> r) -> (q -> r) -> p | q -> r", "_|_ -> p",
])
def test_intuitionistic_theorems_are_found(src):
    f = P(src)
    assert ti.provable(f)
    assert ti.tautology(f)  # soundness: intuitionistic theorems are classical


@pytest.mark.parametrize("src", [
    "((p -> q) -> p) -> p", "~~p -> p", "p | ~p", "(~q -> ~p) -> p -> q",
    "~(p & q) -> ~p | ~q", "(p -> q) | (q -> p)",
])
def test_classical_but_not_intuitionistic(src):
    f = P(src)
    assert ti.tautology(f)
    assert not ti.provable(f)
    # Glivenko: the double negation is intuitionistically provable.
    assert ti.provable(("imp", ("imp", f, ti.BOT), ti.BOT))


def test_invalid_formulas():
    for src in ["(p -> q) -> q -> p", "p", "p -> q", "p | q"]:
        f = P(src)
        assert not ti.tautology(f) and not ti.provable(f)


def test_hypotheses_in_context():
    p, q = ("atom", "p"), ("atom", "q")
    assert ti.provable(q, frozenset({p, ("imp", p, q)}))
    assert not ti.provable(q, frozenset({("imp", p, q)}))


def test_survey_of_implicational_formulas():
    forms = ti.implicational_formulas(4)
    assert len(forms) == 2 + 4 + 16 + 80
    gap = [f for f in forms if ti.tautology(f) and not ti.provable(f)]
    assert sorted(ti.show(f) for f in gap) == [
        "((p → q) → p) → p", "((q → p) → q) → q"]
    # every inhabited implicational type is a tautology
    assert all(ti.tautology(f) for f in forms if ti.provable(f))


def test_show_round_trip():
    for _, src in ti.FAMOUS:
        f = P(src)
        shown = ti.show(f).replace("→", "->").replace("¬", "~") \
            .replace("∧", "&").replace("∨", "|")
        assert P(shown) == f
