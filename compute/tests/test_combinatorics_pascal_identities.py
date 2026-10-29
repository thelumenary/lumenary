import math

import pytest

import combinatorics_pascal_identities as cp


def test_first_rows():
    rows = cp.pascal_rows(5)
    assert rows[0] == [1]
    assert rows[4] == [1, 4, 6, 4, 1]
    assert rows[5] == [1, 5, 10, 10, 5, 1]


def test_rule_matches_math_comb():
    rows = cp.pascal_rows(30)
    for n, row in enumerate(rows):
        assert row == [math.comb(n, k) for k in range(n + 1)]


@pytest.mark.parametrize("n,k,expected", [(5, 2, 10), (6, 0, 1), (6, 6, 1),
                                          (10, 3, 120), (4, 5, 0)])
def test_count_subsets(n, k, expected):
    assert cp.count_subsets(n, k) == expected


def test_factorial_formula_edges():
    assert cp.factorial_formula(52, 5) == 2598960
    assert cp.factorial_formula(5, -1) == 0
    assert cp.factorial_formula(5, 6) == 0
    assert cp.factorial_formula(0, 0) == 1


def test_binomial_coefficients_are_rows():
    assert cp.binomial_coefficients(0) == [1]
    assert cp.binomial_coefficients(4) == [1, 4, 6, 4, 1]
    rows = cp.pascal_rows(8)
    assert all(cp.binomial_coefficients(n) == rows[n] for n in range(9))


def test_row_identities_detect_errors():
    assert all(cp.row_identities_hold(r) for r in cp.pascal_rows(20))
    assert not cp.row_identities_hold([1, 3, 2, 1])
    assert not cp.row_identities_hold([1, 2, 2, 1])
