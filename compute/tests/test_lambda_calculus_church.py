import pytest

import lambda_calculus_church as lc


@pytest.fixture(scope="module")
def defs():
    return lc.standard_defs()


def test_parse_uses_de_bruijn_indices():
    assert lc.parse(r"\x. x") == ("lam", ("var", 0))
    assert lc.parse(r"λx. λy. x") == ("lam", ("lam", ("var", 1)))
    # alpha-equivalent terms parse to the same de Bruijn term
    assert lc.parse(r"\a. \b. a b") == lc.parse(r"\x. \y. x y")
    # application is left-associative
    assert lc.parse(r"\f. \x. \y. f x y") == (
        "lam", ("lam", ("lam", ("app", ("app", ("var", 2), ("var", 1)),
                                ("var", 0)))))
    with pytest.raises(ValueError):
        lc.parse(r"\x. y")


def test_substitution_avoids_capture():
    # (λx. λy. x) applied to a free variable z (index 0 outside) must give
    # λy. z, i.e. the body λ. var 1 -- not the identity λ. var 0.
    k = lc.parse(r"\x. \y. x")
    free_z = ("var", 0)
    result = lc.beta(k[1], free_z)
    assert result == ("lam", ("var", 1))
    assert result != ("lam", ("var", 0))


def test_church_numerals_round_trip():
    for n in range(8):
        assert lc.decode_church(lc.church(n)) == n
    assert lc.decode_church(lc.parse(r"\f. \x. x")) == 0
    assert lc.decode_church(lc.parse(r"\x. x")) is None
    assert lc.decode_church(None) is None


@pytest.mark.parametrize(
    "src, value",
    [("PLUS 2 3", 5), ("TIMES 2 3", 6), ("EXP 2 3", 8), ("EXP 3 2", 9),
     ("SUCC 4", 5), ("PRED 3", 2), ("PRED 0", 0), ("FACT 3", 6)],
)
def test_arithmetic(defs, src, value):
    nf, _ = lc.run(src, defs)
    assert lc.decode_church(nf) == value


def test_step_counts_match_the_lean_evaluator(defs):
    # Lean's `normalize` takes 6 steps for 2 + 3 and 7 for 2 * 3 (normal order).
    assert lc.run("PLUS 2 3", defs)[1] == 6
    assert lc.run("TIMES 2 3", defs)[1] == 7


def test_booleans(defs):
    t, f = defs["TRUE"], defs["FALSE"]
    table = {("TRUE", "TRUE"): t, ("TRUE", "FALSE"): f,
             ("FALSE", "TRUE"): f, ("FALSE", "FALSE"): f}
    for (p, q), expected in table.items():
        assert lc.run(f"AND {p} {q}", defs)[0] == expected
    assert lc.run("NOT TRUE", defs)[0] == f
    assert lc.run("OR FALSE TRUE", defs)[0] == t
    assert lc.run("ISZERO 0", defs)[0] == t
    assert lc.run("ISZERO 2", defs)[0] == f


def test_omega_loops_and_strategy_matters(defs):
    omega = defs["OMEGA"]
    assert lc.step_normal(omega) == omega
    assert lc.normalize(omega, 200) == (None, 200)
    nf, steps = lc.run("K I OMEGA", defs)
    assert nf == defs["I"] and steps == 2
    assert lc.run("K I OMEGA", defs, step=lc.step_applicative, fuel=200)[0] is None


def test_applicative_order_agrees_when_it_terminates(defs):
    for src in ["PLUS 2 3", "TIMES 2 2", "AND TRUE FALSE"]:
        assert lc.run(src, defs, step=lc.step_applicative)[0] == lc.run(src, defs)[0]
