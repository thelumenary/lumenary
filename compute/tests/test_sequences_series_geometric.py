from fractions import Fraction

import pytest

import sequences_series_geometric as ex

HALF = Fraction(1, 2)


def test_partial_sums_of_halves():
    sums = ex.partial_sums(Fraction(1), HALF, 6)
    assert sums == [Fraction(2 ** n - 1, 2 ** (n - 1)) for n in range(1, 7)]
    assert ex.partial_sums(Fraction(1), HALF, 0) == []
    with pytest.raises(ValueError):
        ex.partial_sums(1, HALF, -1)


@pytest.mark.parametrize("r", [HALF, -HALF, Fraction(3), Fraction(-7, 8), Fraction(1)])
def test_closed_form_matches_term_by_term(r):
    a = Fraction(5, 3)
    sums = ex.partial_sums(a, r, 25)
    for n in range(1, 26):
        assert sums[n - 1] == ex.closed_form(a, r, n)


def test_gaps_are_exact():
    assert ex.gap(Fraction(1), HALF, 0) == 2
    for n in range(1, 15):
        assert ex.gap(Fraction(1), HALF, n) == Fraction(1, 2 ** (n - 1))
    for n in range(0, 15):
        assert ex.gap(Fraction(9, 10), Fraction(1, 10), n) == Fraction(1, 10 ** n)


def test_terms_needed():
    assert ex.terms_needed(Fraction(1), HALF, Fraction(1, 10 ** 6)) == 21
    assert ex.terms_needed(Fraction(9, 10), Fraction(1, 10), Fraction(1, 1000)) == 4
    with pytest.raises(ValueError):
        ex.terms_needed(1, 1, Fraction(1, 10))


def test_divergent_cases():
    assert ex.partial_sums(1, -1, 6) == [1, 0, 1, 0, 1, 0]
    assert ex.partial_sums(1, 2, 5) == [1, 3, 7, 15, 31]
    assert ex.closed_form(4, 1, 10) == 40
