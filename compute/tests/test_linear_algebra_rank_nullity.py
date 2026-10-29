import random
from fractions import Fraction

import pytest

import linear_algebra_rank_nullity as ex


def test_worked_example_rref_and_null_space():
    reduced, pivots = ex.rref([[1, 2, 1, 4], [2, 4, 3, 9]])
    assert pivots == [0, 2]
    assert reduced == [[1, 2, 0, 3], [0, 0, 1, 1]]
    assert ex.null_space([[1, 2, 1], [2, 4, 3]]) == [[-2, 1, 0]]
    assert ex.rank([[1, 2, 1], [2, 4, 3]]) == 2


@pytest.mark.parametrize(
    "matrix, expected",
    [
        ([[0, 0], [0, 0]], 0),
        ([[1, 0], [0, 1]], 2),
        ([[1, 2, 3], [2, 4, 6], [1, 0, 1]], 2),
        ([[2, 4], [1, 2], [3, 6]], 1),
        ([[1, 1, 1], [1, 2, 3], [1, 4, 9]], 3),
    ],
)
def test_rank_known_values(matrix, expected):
    assert ex.rank(matrix) == expected
    assert ex.rank(matrix) + len(ex.null_space(matrix)) == len(matrix[0])


def test_rref_uses_exact_fractions():
    reduced, _ = ex.rref([[3, 1], [1, 3]])
    assert reduced == [[1, 0], [0, 1]]
    assert all(isinstance(x, Fraction) for row in reduced for x in row)
    # A matrix that floating point elimination handles badly is exact here.
    assert ex.rank([[1, Fraction(1, 3)], [3, 1]]) == 1


def test_null_space_vectors_solve_and_are_independent():
    a = [[1, 2, 0, -1], [0, 0, 1, 2]]
    basis = ex.null_space(a)
    assert len(basis) == 2
    for v in basis:
        assert ex.mat_vec(a, v) == [0, 0]
    # Independent: each has a 1 in its own free column where the others have 0.
    assert ex.rank(basis) == 2


def test_random_products_have_rank_at_most_r():
    rng = random.Random(7)
    for _ in range(50):
        m, n = rng.randint(2, 5), rng.randint(2, 6)
        r = rng.randint(1, min(m, n))
        mat = ex.random_matrix_of_rank(rng, m, n, r)
        assert len(mat) == m and len(mat[0]) == n
        assert ex.rank(mat) <= r
        assert ex.check_rank_nullity(mat)


def test_mat_mul_small():
    assert ex.mat_mul([[1, 2], [3, 4]], [[0, 1], [1, 0]]) == [[2, 1], [4, 3]]
    assert ex.mat_mul([[0, 1], [0, 0]], [[0, 0], [1, 0]]) != ex.mat_mul([[0, 0], [1, 0]], [[0, 1], [0, 0]])
