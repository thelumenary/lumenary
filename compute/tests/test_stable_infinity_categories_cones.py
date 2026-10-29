from fractions import Fraction

import pytest

import stable_infinity_categories_cones as sc


def test_rank_and_matmul():
    assert sc.rank(sc.q([1, 2], [2, 4])) == 1
    assert sc.rank(sc.q([1, 0], [0, 1])) == 2
    assert sc.rank(sc.zeros(2, 3)) == 0
    assert sc.matmul(sc.q([1, 2]), sc.q([3], [4]), 2, 1) == [[Fraction(11)]]
    assert sc.matmul(sc.zeros(2, 0), sc.zeros(0, 3), 0, 3) == sc.zeros(2, 3)


def test_betti_numbers_of_simple_complexes():
    # Q -> Q by 2 is acyclic over Q; the zero map gives homology in both degrees.
    assert sc.betti(sc.Complex({1: 1, 0: 1}, {1: sc.q([2])})) == {}
    assert sc.betti(sc.Complex({1: 1, 0: 1})) == {0: 1, 1: 1}
    assert sc.betti(sc.Complex({})) == {}


@pytest.mark.parametrize("name", list(sc.EXAMPLES))
def test_cone_is_a_complex_and_detects_quasi_isomorphisms(name):
    x, y, f = sc.EXAMPLES[name]
    assert sc.is_chain_map(f, x, y)
    c = sc.cone(f, x, y)
    assert sc.is_complex(c)
    # Euler characteristic is additive: chi(Cone f) = chi(Y) - chi(X).
    chi = lambda cx: sum((-1) ** n * d for n, d in sc.betti(cx).items())
    assert chi(c) == chi(y) - chi(x)
    quasi_iso = "not a q-iso" not in name
    assert (sc.betti(c) == {}) == quasi_iso


def test_cone_of_identity_is_acyclic():
    x = sc.Complex({1: 2, 0: 1}, {1: sc.q([1, 1])})
    ident = {n: [[Fraction(int(i == j)) for j in range(x.dim(n))]
                 for i in range(x.dim(n))] for n in x.dims}
    c = sc.cone(ident, x, x)
    assert sc.is_complex(c)
    assert sc.betti(c) == {}


def test_non_chain_map_is_detected():
    x = sc.Complex({1: 1, 0: 1}, {1: sc.q([1])})
    y = sc.Complex({1: 1, 0: 1}, {1: sc.q([1])})
    assert not sc.is_chain_map({1: sc.q([1]), 0: sc.q([2])}, x, y)
    assert sc.is_chain_map({1: sc.q([3]), 0: sc.q([3])}, x, y)


@pytest.mark.parametrize("h", [0, 1, 2, Fraction(-1, 3), 7])
def test_map_on_cones_depends_on_homotopy(h):
    valid, chain, matrix = sc.square_example(h)
    assert valid and chain
    assert matrix == [[Fraction(h)]]


def test_invalid_homotopy_is_rejected():
    # For the identity square on Q[0] -> Q[0], h = 0 works but a nonzero
    # degree-0 "homotopy" into a complex with no degree-1 part is impossible.
    x = sc.Complex({0: 1})
    ident = {0: sc.q([1])}
    assert sc.is_homotopy({}, ident, ident, ident, ident, x, x, x, x)
    assert not sc.is_homotopy({}, ident, {0: sc.q([2])}, ident, ident, x, x, x, x)
