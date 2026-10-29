import pytest

import type_theory_inference as tt


def typ(src):
    return tt.show(tt.infer(tt.parse(src)))


def test_parser():
    assert tt.parse(r"\x y. x") == ("lam", "x", ("lam", "y", ("var", "x")))
    assert tt.parse(r"f x y") == ("app", ("app", ("var", "f"), ("var", "x")), ("var", "y"))
    with pytest.raises(ValueError):
        tt.parse(r"(\x. x")


@pytest.mark.parametrize("src, expected", [
    (r"\x. x", "a → a"),
    (r"\x y. x", "a → b → a"),
    (r"\f g x. f x (g x)", "(a → b → c) → (a → b) → a → c"),
    (r"\f g x. f (g x)", "(a → b) → (c → a) → c → b"),
    (r"\f x. f (f x)", "(a → a) → a → a"),
    (r"\f x. x", "a → b → b"),
    (r"(\x y. x) (\z. z)", "a → b → b"),
])
def test_principal_types(src, expected):
    assert typ(src) == expected


def test_self_application_is_untypable():
    for src in [r"\x. x x", r"\f. (\x. f (x x)) (\x. f (x x))",
                r"(\x. x x) (\x. x x)"]:
        with pytest.raises(tt.Untypable):
            tt.infer(tt.parse(src))


def test_unification_basics():
    sub = {}
    a, b = ("tv", 0), ("tv", 1)
    tt.unify(("fn", a, b), ("fn", b, ("fn", ("tv", 2), ("tv", 2))), sub)
    assert tt.resolve(a, sub) == tt.resolve(b, sub)
    with pytest.raises(tt.Untypable):
        tt.unify(a, ("fn", a, b), {})


def test_every_principal_type_is_a_tautology():
    for _, src in tt.EXAMPLES:
        try:
            ty = tt.infer(tt.parse(src))
        except tt.Untypable:
            continue
        assert tt.tautology(ty)


def test_tautology_check_rejects_non_theorems():
    a, b = ("tv", "a"), ("tv", "b")
    assert not tt.tautology(("fn", a, b))
    peirce = ("fn", ("fn", ("fn", a, b), a), a)
    assert tt.tautology(peirce)  # a tautology, yet no term has this type


def test_free_variables_are_rejected():
    with pytest.raises(ValueError):
        tt.infer(tt.parse(r"\x. y"))
