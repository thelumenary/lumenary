import pytest

import complex_numbers_two_squares as ex


def test_gauss_mul_matches_python_complex():
    for z in ex.grid(3):
        for w in ex.grid(3):
            p = complex(*z) * complex(*w)
            assert ex.gauss_mul(z, w) == (int(p.real), int(p.imag))


def test_i_squared_and_norm():
    assert ex.gauss_mul((0, 1), (0, 1)) == (-1, 0)
    assert ex.norm((3, 4)) == 25
    assert ex.norm((0, 0)) == 0


def test_multiplicative_on_grid():
    cases, failures = ex.check_multiplicative(4)
    assert cases == 81 ** 2
    assert failures == []
    with pytest.raises(ValueError):
        ex.grid(-1)


def test_two_square_reps():
    assert ex.two_square_reps(65) == [(1, 8), (4, 7)]
    assert ex.two_square_reps(25) == [(0, 5), (3, 4)]
    assert ex.two_square_reps(3) == []
    assert ex.two_square_reps(0) == [(0, 0)]
    assert len(ex.two_square_reps(1105)) == 4


def test_products_give_representations():
    z, w = (1, 2), (2, 3)
    assert ex.normalise(ex.gauss_mul(z, w)) == (4, 7)
    assert ex.normalise(ex.gauss_mul(z, (2, -3))) == (1, 8)
    assert ex.show((8, -1)) == "8 - 1i"
    assert ex.square(-4) == "(-4)^2"
