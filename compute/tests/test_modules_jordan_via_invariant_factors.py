import sympy as sp

import modules_jordan_via_invariant_factors as jf

X = jf.X


def test_invariant_factors_divide_and_multiply_to_charpoly():
    rows = [[5, 4, 2, 1], [0, 1, -1, -1], [-1, -1, 3, 0], [1, 1, -1, 2]]
    factors = jf.invariant_factors(rows)
    for a, b in zip(factors, factors[1:]):
        assert sp.rem(sp.expand(b), sp.expand(a), X) == 0
    product = sp.expand(sp.Mul(*factors))
    charpoly = sp.Matrix(rows).charpoly(X).as_expr()
    assert sp.expand(product - charpoly) == 0


def test_identity_and_scalar_matrices():
    assert jf.invariant_factors([[1, 0], [0, 1]]) == [X - 1, X - 1]
    assert jf.invariant_factors([[3]]) == [X - 3]


def test_jordan_block_gives_single_invariant_factor():
    factors = jf.invariant_factors([[2, 1, 0], [0, 2, 1], [0, 0, 2]])
    assert factors[:2] == [1, 1]
    assert sp.expand(factors[2] - (X - 2) ** 3) == 0
    assert jf.predicted_blocks(factors) == [(2, 3)]


def test_nilpotent_examples_are_distinguished():
    n1 = [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]]
    n2 = [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
    assert jf.predicted_blocks(jf.invariant_factors(n1)) == [(0, 2), (0, 2)]
    assert jf.predicted_blocks(jf.invariant_factors(n2)) == [(0, 1), (0, 3)]
    assert jf.sympy_blocks(n1) == [(0, 2), (0, 2)]


def test_rotation_has_no_rational_jordan_form():
    factors = jf.invariant_factors([[0, -1], [1, 0]])
    assert jf.predicted_blocks(factors) is None
    assert sp.expand(factors[-1] - (X ** 2 + 1)) == 0
