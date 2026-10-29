import sympy

import advanced_linear_algebra_jordan as alj

X = alj.X


def test_jordan_block_shape():
    j = alj.jordan_block(5, 3)
    assert j == sympy.Matrix([[5, 1, 0], [0, 5, 1], [0, 0, 5]])
    assert alj.jordan_block(-1, 1) == sympy.Matrix([[-1]])


def test_block_sizes_from_ranks():
    # J3 + J1 for one eigenvalue in a 4-dimensional space: ranks 4, 2, 1, 0.
    assert alj.block_sizes([4, 2, 1, 0]) == [3, 1]
    # A single block of size n: ranks fall by one each time.
    assert alj.block_sizes([4, 3, 2, 1, 0]) == [4]
    # Diagonalisable (all blocks of size 1).
    assert alj.block_sizes([3, 0, 0]) == [1, 1, 1]
    # The lesson's exercise: rank N = 3, N^2 = 1, N^3 = 0 in dimension 5.
    assert alj.block_sizes([5, 3, 1, 0]) == [3, 2]


def test_example_matrix_is_integer_and_similar_to_j():
    a = alj.example_matrix()
    assert all(v.is_integer for v in a)
    assert sympy.factor(a.charpoly(X).as_expr()) == (X - 2) ** 4 * (X + 1)
    assert alj.rank_sequence(a, 2) == [5, 3, 2, 1, 1]
    assert alj.jordan_data(a) == {-1: [1], 2: [3, 1]}


def test_rank_formula_agrees_with_sympy_on_random_conjugates():
    rng = __import__("random").Random(7)
    j = sympy.diag(alj.jordan_block(1, 2), alj.jordan_block(1, 2),
                   alj.jordan_block(3, 1))
    for _ in range(3):
        while True:
            p = sympy.Matrix(5, 5, lambda i, k: rng.randint(-2, 2))
            if p.det() != 0:
                break
        a = p * j * p.inv()
        _, jj = a.jordan_form()
        assert alj.blocks_of_jordan_matrix(jj) == alj.jordan_data(a)
        assert alj.jordan_data(a) == {1: [2, 2], 3: [1]}


def test_cayley_hamilton_and_minimal_polynomial():
    a = alj.example_matrix()
    assert alj.evaluate(a.charpoly(X).as_expr(), a).is_zero_matrix
    m = alj.minimal_polynomial(a)
    assert sympy.expand(m - (X - 2) ** 3 * (X + 1)) == 0
    assert alj.evaluate(m, a).is_zero_matrix
    assert not alj.evaluate((X - 2) ** 2 * (X + 1), a).is_zero_matrix


def test_evaluate_matches_direct_computation():
    a = sympy.Matrix([[1, 2], [3, 4]])
    assert alj.evaluate(X ** 2 + 1, a) == a * a + sympy.eye(2)
    assert alj.evaluate(sympy.Integer(7), a) == 7 * sympy.eye(2)


def test_char_and_minimal_polynomials_do_not_determine_jordan_form():
    b = sympy.diag(alj.jordan_block(0, 2), alj.jordan_block(0, 2))
    c = sympy.diag(alj.jordan_block(0, 2), alj.jordan_block(0, 1),
                   alj.jordan_block(0, 1))
    assert b.charpoly(X) == c.charpoly(X)
    assert alj.minimal_polynomial(b) == alj.minimal_polynomial(c) == X ** 2
    assert alj.jordan_data(b) != alj.jordan_data(c)
