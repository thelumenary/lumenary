from fractions import Fraction

import pytest

import integer_inverses as ii


def test_window():
    assert list(ii.window(0)) == [0]
    assert list(ii.window(2)) == [-2, -1, 0, 1, 2]
    with pytest.raises(ValueError):
        ii.window(-1)


@pytest.mark.parametrize("n", range(-20, 21))
def test_additive_inverse_always_found_and_correct(n):
    m = ii.find_additive_inverse(n, ii.window(20))
    assert m == -n
    assert n + m == 0


def test_additive_inverse_outside_window_is_not_found():
    assert ii.find_additive_inverse(50, ii.window(10)) is None


@pytest.mark.parametrize("n", range(-20, 21))
def test_multiplicative_inverse_only_for_plus_minus_one(n):
    m = ii.find_multiplicative_inverse(n, ii.window(20))
    if n in (1, -1):
        assert m == n and n * m == 1
    else:
        assert m is None


def test_multiplicative_inverse_empty_candidates():
    assert ii.find_multiplicative_inverse(1, []) is None


@pytest.mark.parametrize("q", [Fraction(1), Fraction(-1), Fraction(2), Fraction(-7, 12), Fraction(10**20, 3)])
def test_rational_inverse_is_exact(q):
    inv = ii.rational_inverse(q)
    assert isinstance(inv, Fraction)
    assert q * inv == 1


def test_rational_inverse_accepts_ints_and_rejects_zero():
    assert ii.rational_inverse(4) == Fraction(1, 4)
    assert ii.rational_inverse(0) is None
    assert ii.rational_inverse(Fraction(0, 5)) is None


def test_search_summary():
    additive, multiplicative = ii.search_summary(30, 30)
    assert additive == list(range(-30, 31))
    assert multiplicative == [-1, 1]


def test_search_summary_small_candidate_window_misses_additive_inverses():
    # Searching too narrow a window misses inverses that exist: absence of evidence is not evidence of absence.
    additive, _ = ii.search_summary(5, 2)
    assert additive == [-2, -1, 0, 1, 2]
