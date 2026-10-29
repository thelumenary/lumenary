from fractions import Fraction

import pytest

import functions_and_graphs_inverse_bisection as fib


def test_f_is_strictly_increasing_on_a_grid():
    pts = [Fraction(n, 3) for n in range(-30, 31)]
    vals = [fib.f(x) for x in pts]
    assert all(u < v for u, v in zip(vals, vals[1:]))


def test_bisection_encloses_exact_inverse_values():
    for y, exact in [(2, 1), (10, 2), (30, 3), (-10, -2), (0, 0)]:
        lo, hi = fib.bisect_inverse(fib.f, Fraction(y), -50, 50, 30)
        assert lo <= exact <= hi
        assert hi - lo == Fraction(100, 2 ** 30)


def test_inverse_error_bound_is_honest():
    x, err = fib.inverse(Fraction(39, 8), steps=40)
    assert abs(x - Fraction(3, 2)) <= err
    assert err < Fraction(1, 10 ** 10)


def test_bisection_rejects_bad_bracket():
    with pytest.raises(ValueError):
        fib.bisect_inverse(fib.f, Fraction(100), 0, 1, 10)


def test_collisions():
    grid = [Fraction(n, 2) for n in range(-6, 7)]
    assert len(fib.collisions(lambda t: t * t, grid)) == 6
    assert fib.collisions(lambda t: t * t, [t for t in grid if t >= 0]) == []
    assert fib.collisions(fib.f, grid) == []
