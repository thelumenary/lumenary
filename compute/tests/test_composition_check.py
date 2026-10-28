import pytest

import composition_check as cc


def test_all_functions_counts():
    assert len(cc.all_functions(cc.X)) == 27
    assert len(cc.all_functions([0, 1])) == 4
    assert cc.all_functions([]) == [{}]
    assert len(cc.all_functions([0, 1], ["a", "b", "c"])) == 9


def test_identity():
    assert cc.identity([0, 1, 2]) == {0: 0, 1: 1, 2: 2}
    assert cc.identity([]) == {}


def test_compose_means_first_f_then_g():
    f = {0: 1, 1: 2, 2: 0}
    g = {0: 0, 1: 0, 2: 1}
    assert cc.compose(g, f) == {0: g[1], 1: g[2], 2: g[0]} == {0: 0, 1: 1, 2: 0}


def test_compose_between_different_sets():
    f = {"a": 1, "b": 2}
    g = {1: "x", 2: "y", 3: "z"}
    assert cc.compose(g, f) == {"a": "x", "b": "y"}


def test_compose_undefined_raises():
    with pytest.raises(ValueError):
        cc.compose({0: 0}, {0: 5})


def test_compose_empty_functions():
    assert cc.compose({}, {}) == {}
    assert cc.compose({1: 2}, {}) == {}


def test_show():
    assert cc.show({0: 1, 1: 0, 2: 2}) == "[1, 0, 2]"


@pytest.mark.parametrize("domain", [[], [0], [0, 1], [0, 1, 2]])
def test_associativity_and_identity_laws_exhaustively(domain):
    functions = cc.all_functions(domain)
    triples, failures = cc.check_associativity(functions)
    assert triples == len(functions) ** 3 and failures == []
    checked, failures = cc.check_identity_laws(functions, domain)
    assert checked == len(functions) and failures == []


def test_check_associativity_detects_a_non_associative_operation(monkeypatch):
    # Pointwise subtraction mod 3 is not associative: h - (g - f) != (h - g) - f when f != 0.
    # (Beware: a wrong "composition" such as (g, f) -> g IS associative, so it would not fail.)
    monkeypatch.setattr(cc, "compose", lambda g, f: {x: (g[x] - f[x]) % 3 for x in f})
    triples, failures = cc.check_associativity(cc.all_functions([0, 1, 2]))
    assert triples == 27 ** 3
    assert len(failures) == 27 * 27 * 26  # every triple whose f is not the zero function


def test_noncommuting_pair_is_genuine():
    f, g = cc.first_noncommuting_pair(cc.all_functions(cc.X))
    assert cc.compose(g, f) != cc.compose(f, g)


def test_one_point_set_everything_commutes():
    assert cc.first_noncommuting_pair(cc.all_functions([0])) is None


def test_commuting_pairs_counts():
    functions = cc.all_functions(cc.X)
    pairs = cc.commuting_pairs(functions)
    assert len(pairs) == 141
    # Every function commutes with itself and with the identity.
    ident = cc.identity(cc.X)
    assert all((f, f) in pairs and (f, ident) in pairs for f in functions)
    assert len(cc.commuting_pairs(cc.all_functions([0, 1]))) == 10


def test_swap_and_rotation_do_not_commute():
    swap, rot = {0: 1, 1: 0, 2: 2}, {0: 1, 1: 2, 2: 0}
    assert cc.compose(rot, swap) == {0: 2, 1: 1, 2: 0}
    assert cc.compose(swap, rot) == {0: 0, 1: 2, 2: 1}
