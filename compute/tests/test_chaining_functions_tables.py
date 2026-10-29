from fractions import Fraction
from itertools import product

import pytest

import chaining_functions_tables as cf


def test_then_follows_f_first():
    f = {1: "a", 2: "b"}
    g = {"a": "x", "b": "y"}
    assert cf.then(f, g) == {1: "x", 2: "y"}
    add3 = {x: x + 3 for x in range(5)}
    double = {x: 2 * x for x in range(10)}
    assert cf.then(add3, double)[1] == 8  # 2 * (1 + 3)
    assert cf.then({1: 2}, {2: 3, 4: 5}) == {1: 3}


def test_chain_needs_outputs_to_be_inputs():
    with pytest.raises(ValueError):
        cf.then({1: 5}, {2: 3})
    assert set(cf.then(cf.HOME_CITY, cf.CONTINENT).values()) <= set(cf.CONTINENT.values())


def test_identity_and_undoing():
    ident = cf.identity([0, 1, 2])
    f = {0: 1, 1: 2, 2: 0}
    assert cf.then(ident, f) == f == cf.then(f, ident)
    g = {1: 0, 2: 1, 0: 2}
    assert cf.undoes(g, f) and cf.undoes(f, g)
    square = {x: x * x for x in range(-2, 3)}
    assert cf.undoing_function(square, list(range(-2, 3))) is None


def test_counts_on_three_elements():
    elems = [0, 1, 2]
    funcs = list(cf.all_functions(elems))
    assert len(funcs) == 27
    undoable = [f for f in funcs if cf.undoing_function(f, elems) is not None]
    assert len(undoable) == 6
    assert all(len(set(f.values())) == 3 for f in undoable)  # exactly the bijections
    commuting = sum(cf.then(f, g) == cf.then(g, f) for f in funcs for g in funcs)
    assert commuting == 141


def test_socks_and_shoes_and_wrong_order():
    elems = [0, 1, 2]
    pairs = [(f, cf.undoing_function(f, elems)) for f in cf.all_functions(elems)]
    pairs = [(f, u) for f, u in pairs if u is not None]
    for (f, uf), (g, ug) in product(pairs, repeat=2):
        assert cf.undoes(cf.then(ug, uf), cf.then(f, g))
        wrong_works = cf.undoes(cf.then(uf, ug), cf.then(f, g))
        assert wrong_works == (cf.then(f, g) == cf.then(g, f))


def test_temperatures_exact():
    assert cf.to_fahrenheit(30) == 86
    assert cf.to_fahrenheit(-40) == -40
    assert cf.to_fahrenheit(100) == 212
    for c in [Fraction(-17, 3), 0, 37, Fraction(1, 7)]:
        assert cf.to_celsius(cf.to_fahrenheit(c)) == c
    assert cf.wrong_undo(cf.to_fahrenheit(30)) == Fraction(142, 9)
    assert cf.wrong_undo(cf.to_fahrenheit(0)) == Fraction(-128, 9)
