from fractions import Fraction

import pytest

import measure_theory_cantor_set as cs


def test_stage_counts_and_lengths():
    for n in range(8):
        stage = cs.cantor_stage(n)
        assert len(stage) == 2 ** n
        assert cs.total_length(stage) == Fraction(2, 3) ** n
    with pytest.raises(ValueError):
        cs.cantor_stage(-1)


def test_stage_intervals_are_disjoint_and_sorted():
    stage = cs.cantor_stage(5)
    for (a, b), (c, d) in zip(stage, stage[1:]):
        assert a < b < c < d


def test_membership_rule_matches_intervals():
    stage = cs.cantor_stage(4)
    for k in range(0, 82):
        x = Fraction(k, 81)
        in_intervals = any(a <= x <= b for a, b in stage)
        assert cs.in_stage(x, 4) == in_intervals
    assert not cs.in_stage(Fraction(1, 2), 1)
    assert not cs.in_stage(Fraction(-1, 3), 0)


def test_quarter_is_in_the_cantor_set_but_not_an_endpoint():
    q = Fraction(1, 4)
    assert all(cs.in_stage(q, n) for n in range(60))
    assert cs.ternary_digits(q, 6) == [0, 2, 0, 2, 0, 2]
    assert q not in cs.endpoints(10)
    assert Fraction(1, 3) in cs.endpoints(1)


def test_injection_from_bit_strings():
    strings = [[(m >> i) & 1 for i in range(8)] for m in range(256)]
    points = [cs.bits_to_cantor_point(s) for s in strings]
    assert len(set(points)) == 256
    assert all(cs.in_stage(p, 8) for p in points)
    assert cs.bits_to_cantor_point([1, 1, 1]) == Fraction(26, 27)


def test_first_stage_below():
    assert cs.first_stage_below(Fraction(1, 1000)) == 18
    assert Fraction(2, 3) ** 17 >= Fraction(1, 1000) > Fraction(2, 3) ** 18
    assert cs.first_stage_below(Fraction(2)) == 0
