import sympy

import ordinary_differential_equations_picard_iteration as pi

t = pi.t


def test_picard_for_exponential_gives_taylor_polynomials():
    xs = pi.picard_iterates(lambda s, x: x, 1, 6)
    for k, xk in enumerate(xs):
        taylor = sum(t**j / sympy.factorial(j) for j in range(k + 1))
        assert sympy.expand(xk - taylor) == 0


def test_first_iterate_is_integral_of_constant():
    xs = pi.picard_iterates(lambda s, x: 3 * x, 2, 1)
    assert sympy.expand(xs[1] - (2 + 6 * t)) == 0


def test_agreement_order():
    assert pi.agreement_order(1 + t + t**2 / 2, sympy.exp(t)) == 2
    assert pi.agreement_order(1 + t, 1 / (1 - t)) == 1
    assert pi.agreement_order(sympy.Integer(1), sympy.exp(t)) == 0


def test_linear_problem_iterates_agree_with_solution_to_increasing_order():
    exact = 2 * sympy.exp(t) - t - 1
    ys = pi.picard_iterates(lambda s, x: s + x, 1, 5)
    orders = [pi.agreement_order(y, exact) for y in ys[1:]]
    assert orders == [1, 2, 3, 4, 5]


def test_square_problem_degrees_double_and_series_matches():
    zs = pi.picard_iterates(lambda s, x: x**2, 1, 4)
    degrees = [int(sympy.degree(z, t)) for z in zs[1:]]
    assert degrees == [1, 3, 7, 15]
    assert pi.agreement_order(zs[4], 1 / (1 - t)) == 4
    # Iterates satisfy the integral equation's recursion x_{k+1}' = x_k^2.
    for k in range(3):
        assert sympy.expand(sympy.diff(zs[k + 1], t) - zs[k] ** 2) == 0
