import cmath
import math

import pytest
import sympy

import complex_numbers_roots_of_unity as ex


@pytest.mark.parametrize("n", range(1, 13))
def test_roots_are_on_unit_circle_and_solve_equation(n):
    zs = ex.roots_of_unity(n)
    assert len(zs) == n
    assert all(abs(abs(z) - 1) < 1e-12 for z in zs)
    assert ex.max_error_power(n) < 1e-12


@pytest.mark.parametrize("n", range(2, 13))
def test_sum_zero_product_sign_and_spacing(n):
    assert abs(ex.root_sum(n)) < 1e-12
    assert abs(ex.root_product(n) - (-1) ** (n + 1)) < 1e-12
    assert math.isclose(ex.side_length(n), 2 * math.sin(math.pi / n), rel_tol=1e-12)


def test_validation_and_trivial_case():
    with pytest.raises(ValueError):
        ex.roots_of_unity(0)
    assert ex.roots_of_unity(1) == [1 + 0j]
    assert abs(ex.root_sum(1) - 1) < 1e-15


def test_exact_cube_roots():
    roots = ex.exact_cube_roots()
    assert roots[0] == 1
    assert len(roots) == 3
    for r in roots:
        assert sympy.simplify(sympy.expand(r ** 3) - 1) == 0
    assert sympy.simplify(sum(roots)) == 0


def test_triple_angle_formulas():
    re_part, im_part = ex.triple_angle()
    t = sympy.symbols("t", real=True)
    assert sympy.simplify(re_part - sympy.cos(3 * t)) == 0
    assert sympy.simplify(im_part - sympy.sin(3 * t)) == 0
    assert re_part == 4 * sympy.cos(t) ** 3 - 3 * sympy.cos(t)


def test_square_root_trap():
    assert cmath.sqrt(-1) * cmath.sqrt(-1) == -1
    assert cmath.sqrt((-1) * (-1)) == 1
