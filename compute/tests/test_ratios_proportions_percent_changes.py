from fractions import Fraction

import pytest

import ratios_proportions_percent_changes as rp


def test_factor_and_combined():
    assert rp.factor(10) == Fraction(11, 10)
    assert rp.factor(-25) == Fraction(3, 4)
    assert rp.combined() == 1
    assert rp.combined(10, -10) == Fraction(99, 100)
    assert rp.combined(10, 10, 10, 10, 10) == Fraction(161051, 100000)


def test_up_down_is_one_minus_square():
    for p in range(-99, 150):
        r = Fraction(p, 100)
        assert rp.combined(p, -p) == 1 - r * r


def test_order_does_not_matter_with_fractional_percentages():
    for p, q in [(Fraction(5, 2), -40), (12, Fraction(-7, 3)), (300, -75)]:
        assert rp.combined(p, q) == rp.combined(q, p)


def test_as_percent_change():
    assert rp.as_percent_change(Fraction(99, 100)) == -1
    assert rp.as_percent_change(Fraction(3, 2)) == 50


def test_undo_rise():
    assert rp.undo_rise(25) == 20
    assert rp.undo_rise(100) == 50
    assert rp.undo_rise(10) == Fraction(100, 11)
    for p in [1, 7, 25, 60, 250]:
        assert rp.combined(p, -rp.undo_rise(p)) == 1
    with pytest.raises(ValueError):
        rp.undo_rise(-100)


def test_adding_works_only_when_one_change_is_zero():
    hits, tried = rp.when_adding_works(-20, 20)
    assert tried == 41 * 41
    assert len(hits) == 2 * 41 - 1
    assert all(p == 0 or q == 0 for p, q in hits)


def test_fmt():
    assert rp.fmt(Fraction(99, 100)) == "0.99"
    assert rp.fmt(Fraction(4)) == "4"
    assert rp.fmt(Fraction(100, 3)) == "100/3 (about 33.33)"
