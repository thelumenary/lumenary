import math

import pytest

import recurrences_generating_functions_catalan as rc

CATALAN = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]


def test_is_balanced():
    assert rc.is_balanced("")
    assert rc.is_balanced("(()())")
    assert not rc.is_balanced(")(")
    assert not rc.is_balanced("(()")
    assert not rc.is_balanced("())(")


def test_brute_force_small():
    assert [rc.brute_force_count(n) for n in range(7)] == CATALAN[:7]


def test_segner_and_closed_form_agree():
    assert rc.segner(11) == CATALAN
    assert all(rc.closed_form(n) == c for n, c in enumerate(rc.segner(40)))
    assert rc.closed_form(5) == 42


@pytest.mark.parametrize("rounds", [1, 4, 9])
def test_fixed_point_fixes_one_coefficient_per_round(rounds):
    c = rc.series_fixed_point(12, rounds)
    # after r rounds, at least the first r coefficients are correct
    assert c[:rounds] == CATALAN[:rounds]


def test_fixed_point_converges():
    assert rc.series_fixed_point(11, 11) == CATALAN


def test_asymptotic_ratio_tends_to_one():
    r10, r100, r1000 = (rc.asymptotic_ratio(n) for n in (10, 100, 1000))
    assert r10 < r100 < r1000 < 1
    assert abs(r1000 - (1 - 9 / 8000)) < 1e-5
    exact = math.comb(20, 10) // 11
    assert abs(rc.asymptotic_ratio(10) - exact / (4 ** 10 / (math.sqrt(math.pi) * 10 ** 1.5))) < 1e-9
