import pytest

import algebraic_number_theory_class_numbers as cn


def test_fundamental_discriminants():
    assert cn.is_fundamental(-3) and cn.is_fundamental(-4)
    assert cn.is_fundamental(-20) and cn.is_fundamental(-8)
    assert not cn.is_fundamental(-12)      # -12 = 4 * (-3), -3 = 1 mod 4
    assert not cn.is_fundamental(-16)
    assert not cn.is_fundamental(-6)       # -6 = 2 mod 4


def test_known_class_numbers():
    known = {-3: 1, -4: 1, -7: 1, -8: 1, -15: 2, -20: 2, -23: 3, -47: 5,
             -71: 7, -163: 1, -191: 13}
    for D, h in known.items():
        assert cn.class_number(D) == h, D


def test_reduced_forms_of_minus_twenty():
    assert cn.reduced_forms(-20) == [(1, 0, 5), (2, 2, 3)]
    for a, b, c in cn.reduced_forms(-84):
        assert b * b - 4 * a * c == -84 and abs(b) <= a <= c


def test_dirichlet_formula_agrees():
    for D in range(-300, 0):
        if cn.is_fundamental(D):
            assert cn.class_number_formula(D) == cn.class_number(D), D


def test_heegner_numbers():
    ones = [D for D in range(-400, 0) if cn.is_fundamental(D)
            and cn.class_number(D) == 1]
    assert sorted(ones) == [-163, -67, -43, -19, -11, -8, -7, -4, -3]


def test_kronecker_symbol():
    assert cn.kronecker(-4, 3) == -1 and cn.kronecker(-4, 5) == 1
    assert cn.kronecker(-4, 2) == 0
    assert cn.kronecker(5, 2) == -1 and cn.kronecker(-7, 2) == 1
    assert cn.kronecker(-20, 9) == 1           # multiplicative: (-20/3)^2


@pytest.mark.parametrize("d,unit", [(2, (1, 1, -1)), (3, (2, 1, 1)),
                                    (61, (29718, 3805, -1)),
                                    (94, (2143295, 221064, 1))])
def test_fundamental_units(d, unit):
    x, y, n = cn.fundamental_unit(d)
    assert (x, y, n) == unit
    assert x * x - d * y * y == n
