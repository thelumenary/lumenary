import math
from fractions import Fraction

import pytest
import sympy

import intro_calculus_difference_quotients as ex


@pytest.mark.parametrize("a", [Fraction(0), Fraction(3), Fraction(-5, 2)])
@pytest.mark.parametrize("h", [Fraction(1), Fraction(1, 7), Fraction(-1, 1000)])
def test_square_quotient_is_exactly_2a_plus_h(a, h):
    assert ex.forward_quotient(ex.square, a, h) == 2 * a + h


def test_central_quotient_of_square_is_exact():
    # For x^2 the symmetric quotient has no error at all: it equals 2a.
    for a in [Fraction(1), Fraction(-4, 3)]:
        for h in [Fraction(1, 2), Fraction(1, 99)]:
            assert ex.central_quotient(ex.square, a, h) == 2 * a


def test_zero_step_rejected():
    with pytest.raises(ValueError):
        ex.forward_quotient(ex.square, 1, 0)
    with pytest.raises(ValueError):
        ex.central_quotient(ex.square, 1, 0)


def test_error_shrinks_then_rounding_takes_over():
    rows = ex.quotient_errors([1, 3, 5, 13])
    fwd = [r[1] for r in rows]
    cen = [r[2] for r in rows]
    assert fwd[0] > fwd[1] > fwd[2]          # truncation error ~ h
    assert cen[0] > cen[1] > cen[2]          # truncation error ~ h^2
    assert fwd[3] > fwd[2] and cen[3] > cen[2]   # rounding wins at h = 1e-13
    assert math.isclose(fwd[1] / fwd[0], 0.01, rel_tol=0.05)


def test_symbolic_results():
    lim, deriv = ex.symbolic_results()
    x = sympy.symbols("x")
    n = sympy.symbols("n", positive=True, integer=True)
    assert lim == sympy.cos(1)
    assert sympy.simplify(deriv - n * x ** (n - 1)) == 0
