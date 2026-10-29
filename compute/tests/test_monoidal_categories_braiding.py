import sympy

import monoidal_categories_braiding as mb

Q = mb.Q


def test_r_matrix_at_one_is_the_swap():
    assert mb.r_matrix(1) == mb.swap()
    assert mb.swap() * mb.swap() == sympy.eye(4)


def test_braid_relation_holds_symbolically_and_for_swap():
    zero = sympy.zeros(8, 8)
    assert mb.braid_defect(mb.r_matrix(Q)) == zero
    assert mb.braid_defect(mb.swap()) == zero
    assert mb.braid_defect(mb.r_matrix(sympy.Rational(3, 2))) == zero


def test_hecke_relation_and_square():
    r = mb.r_matrix(Q)
    assert mb.hecke_defect(r, Q) == sympy.zeros(4, 4)
    diff = mb.square_minus_identity(r)
    assert sympy.simplify(diff - (Q - 1 / Q) * r) == sympy.zeros(4, 4)


def test_not_symmetric_unless_q_squared_is_one():
    for q in [2, 3, sympy.Rational(1, 2), sympy.I]:
        assert mb.square_minus_identity(mb.r_matrix(q)) != sympy.zeros(4, 4)
    for q in [1, -1]:
        assert mb.square_minus_identity(mb.r_matrix(q)) == sympy.zeros(4, 4)


def test_a_random_invertible_matrix_is_not_a_braiding():
    m = sympy.Matrix([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 1], [0, 0, 0, 1]])
    assert m.det() != 0
    assert mb.braid_defect(m) != sympy.zeros(8, 8)


def test_kronecker_placement():
    m = mb.swap()
    a = mb.on_first_two(m)
    b = mb.on_last_two(m)
    assert a.shape == b.shape == (8, 8)
    # swapping factors 1,2 then 2,3 then 1,2 reverses e1 e1 e2 -> e2 e1 e1
    v = sympy.zeros(8, 1)
    v[1] = 1  # e1 (x) e1 (x) e2 has index 0*4 + 0*2 + 1 = 1
    w = a * b * a * v
    assert w[4] == 1  # e2 (x) e1 (x) e1 has index 4
