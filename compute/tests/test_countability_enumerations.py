from fractions import Fraction

import pytest

import countability_enumerations as ce


def test_zigzag_is_a_bijection_onto_an_interval():
    values = [ce.zigzag(n) for n in range(201)]
    assert values[:7] == [0, -1, 1, -2, 2, -3, 3]
    assert sorted(values) == list(range(-100, 101))
    with pytest.raises(ValueError):
        ce.zigzag(-1)


def test_cantor_pair_small_values():
    assert [ce.cantor_pair(0, 0), ce.cantor_pair(1, 0), ce.cantor_pair(0, 1)] == [0, 1, 2]
    assert ce.cantor_pair(2, 3) == 18
    # The first T(d) = d(d+1)/2 values fill exactly the first d diagonals.
    d = 30
    values = {ce.cantor_pair(m, n) for m in range(d) for n in range(d) if m + n < d}
    assert values == set(range(d * (d + 1) // 2))


def test_unpair_inverts_pair():
    for k in range(20_000):
        assert ce.cantor_pair(*ce.cantor_unpair(k)) == k
    for m in range(60):
        for n in range(60):
            assert ce.cantor_unpair(ce.cantor_pair(m, n)) == (m, n)
    with pytest.raises(ValueError):
        ce.cantor_unpair(-3)


def test_calkin_wilf_start_and_distinctness():
    terms = ce.calkin_wilf(1023)
    assert terms[:7] == [Fraction(1), Fraction(1, 2), Fraction(2), Fraction(1, 3),
                         Fraction(3, 2), Fraction(2, 3), Fraction(3)]
    assert len(set(terms)) == len(terms)
    assert all(x > 0 for x in terms)


def test_calkin_wilf_tree_rows():
    # Row k of the Calkin-Wilf tree (terms 2^k .. 2^(k+1) - 1) holds the 2^k
    # fractions whose continued fraction digits sum to k + 1; check sizes and
    # that 1/n and n appear at the ends of row n - 1.
    terms = ce.calkin_wilf(2 ** 8 - 1)
    for k in range(8):
        row = terms[2 ** k - 1: 2 ** (k + 1) - 1]
        assert len(row) == 2 ** k
        assert row[0] == Fraction(1, k + 1) and row[-1] == Fraction(k + 1)


def test_first_time_all_seen():
    terms = ce.calkin_wilf(2047)
    assert ce.first_time_all_seen(terms, 1) == 1
    assert ce.first_time_all_seen(terms, 10) == 1023
    assert ce.first_time_all_seen(terms[:100], 10) is None
