import sympy

import differential_forms_exterior_calculus as ec

x, y, z = ec.X


def test_sort_sign():
    assert ec.sort_sign((0, 1)) == (1, (0, 1))
    assert ec.sort_sign((1, 0)) == (-1, (0, 1))
    assert ec.sort_sign((2, 0, 1)) == (1, (0, 1, 2))
    assert ec.sort_sign((1, 0, 2)) == (-1, (0, 1, 2))
    assert ec.sort_sign((1, 1)) == (0, ())


def test_basic_wedges():
    dx, dy, dz = {(0,): 1}, {(1,): 1}, {(2,): 1}
    assert ec.wedge(dx, dy) == {(0, 1): 1}
    assert ec.wedge(dy, dx) == {(0, 1): -1}
    assert ec.wedge(dx, dx) == {}
    assert ec.wedge(ec.wedge(dz, dx), dy) == {(0, 1, 2): 1}


def test_d_of_functions_and_dd_zero():
    f = x ** 2 * y + sympy.sin(z)
    assert ec.d({(): f}) == {(0,): 2 * x * y, (1,): x ** 2, (2,): sympy.cos(z)}
    for k in range(3):
        assert ec.d(ec.d(ec.generic(k, "w"))) == {}


def test_graded_commutativity_and_leibniz():
    a, b, c = ec.generic(1, "a"), ec.generic(1, "b"), ec.generic(2, "c")
    assert ec.add(ec.wedge(a, b), ec.wedge(b, a)) == {}
    assert ec.add(ec.wedge(a, c), ec.scale(-1, ec.wedge(c, a))) == {}
    lhs = ec.d(ec.wedge(a, c))
    rhs = ec.add(ec.wedge(ec.d(a), c), ec.scale(-1, ec.wedge(a, ec.d(c))))
    assert ec.add(lhs, ec.scale(-1, rhs)) == {}


def test_closed_but_not_exact_form_is_closed():
    r2 = x ** 2 + y ** 2
    dtheta = {(0,): -y / r2, (1,): x / r2}
    assert {k: sympy.simplify(v) for k, v in ec.d(dtheta).items() if sympy.simplify(v) != 0} == {}


def test_short_printing():
    f = sympy.Function("f")(x, y, z)
    assert ec.short(sympy.diff(f, x)) == "f_x"
    assert ec.show({}) == "0"
