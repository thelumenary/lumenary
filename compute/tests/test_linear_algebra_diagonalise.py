import sympy

import linear_algebra_diagonalise as ex


def test_classify_examples():
    assert ex.classify(2, 0, 0, 3) == "distinct real"
    assert ex.classify(0, -1, 1, 0) == "complex"
    assert ex.classify(3, 0, 0, 3) == "scalar"
    assert ex.classify(0, 1, 0, 0) == "defective"
    assert ex.classify(1, 1, 0, 1) == "defective"
    assert ex.classify(1, 1, 0, 2) == "distinct real"


def test_census_totals_and_values():
    counts = ex.census(range(-2, 3))
    assert sum(counts.values()) == 625
    assert counts == {"distinct real": 416, "complex": 148, "scalar": 5, "defective": 56}
    # Over {0, 1} there are 16 matrices; scalar ones are 0 and I.
    small = ex.census(range(2))
    assert sum(small.values()) == 16 and small["scalar"] == 2


def test_classify_agrees_with_sympy():
    for rows in ([[1, 2], [2, 1]], [[1, -1], [1, 1]], [[2, 1], [0, 2]], [[0, 0], [0, 0]], [[1, 2], [3, 4]]):
        m = sympy.Matrix(rows)
        cls = ex.classify(*m)
        diag_real = m.is_diagonalizable(reals_only=True)
        diag_complex = m.is_diagonalizable()
        assert diag_real == (cls in ("distinct real", "scalar"))
        assert diag_complex == (cls != "defective")


def test_fibonacci_and_binet():
    assert [ex.fibonacci(n) for n in range(10)] == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
    for n in range(25):
        assert ex.binet(n) == ex.fibonacci(n)
    assert ex.fibonacci_by_diagonalising(40) == ex.fibonacci(40) == 102334155


def test_multiplicities_of_defective_and_diagonal_matrices():
    assert ex.multiplicities([[0, 1], [0, 0]]) == [(0, 2, 1)]
    assert ex.multiplicities([[5, 0], [0, 5]]) == [(5, 2, 2)]
