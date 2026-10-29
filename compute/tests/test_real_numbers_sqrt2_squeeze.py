from fractions import Fraction

import pytest

import real_numbers_sqrt2_squeeze as ex


def test_push_known_values():
    assert ex.push(Fraction(1)) == Fraction(4, 3)
    assert ex.push(Fraction(2)) == Fraction(3, 2)
    assert ex.push(Fraction(7, 5)) == Fraction(24, 17)


def test_orbit_length_and_validation():
    assert ex.orbit(1, 0) == [Fraction(1)]
    assert len(ex.orbit(2, 5)) == 6
    with pytest.raises(ValueError):
        ex.orbit(1, -1)


@pytest.mark.parametrize("start", [Fraction(1), Fraction(1, 3), Fraction(7, 5)])
def test_below_stays_below_and_increases(start):
    values = ex.orbit(start, 8)
    assert all(ex.square_minus_two(p) < 0 for p in values)
    assert all(a < b for a, b in zip(values, values[1:]))


@pytest.mark.parametrize("start", [Fraction(2), Fraction(10), Fraction(3, 2)])
def test_above_stays_above_and_decreases(start):
    values = ex.orbit(start, 8)
    assert all(ex.square_minus_two(p) > 0 for p in values)
    assert all(a > b for a, b in zip(values, values[1:]))


def test_identity_behind_the_map():
    # p'^2 - 2 = 2 (p^2 - 2) / (p + 2)^2, the identity proved in Lean.
    for p in [Fraction(1), Fraction(5, 3), Fraction(9, 4), Fraction(1, 7)]:
        q = ex.push(p)
        assert ex.square_minus_two(q) == 2 * ex.square_minus_two(p) / (p + 2) ** 2


def test_no_solutions_and_near_misses():
    assert ex.solutions_sq_eq_two_sq(5000) == []
    misses = ex.near_misses(1000)
    assert misses[:5] == [(1, 1), (3, 2), (7, 5), (17, 12), (41, 29)]
    assert all(abs(p * p - 2 * q * q) == 1 for p, q in misses)
    assert (1393, 985) in misses
