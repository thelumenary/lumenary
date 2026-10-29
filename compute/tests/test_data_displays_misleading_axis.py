from fractions import Fraction

import pytest

import data_displays_misleading_axis as ma


def test_drawn_height():
    assert ma.drawn_height(52, 0) == 52
    assert ma.drawn_height(52, 40) == 12
    with pytest.raises(ValueError):
        ma.drawn_height(30, 40)


def test_apparent_ratio_values():
    assert ma.apparent_ratio(52, 48, 0) == Fraction(13, 12)
    assert ma.apparent_ratio(52, 48, 40) == Fraction(3, 2)
    assert ma.apparent_ratio(52, 48, 47) == 5


def test_ratio_grows_as_axis_rises():
    ratios = [ma.apparent_ratio(52, 48, b) for b in range(0, 48)]
    assert all(r1 < r2 for r1, r2 in zip(ratios, ratios[1:]))


def test_text_bars():
    assert ma.text_bar(52, 0, 2) == "#" * 26
    assert ma.text_bar(48, 40, Fraction(1, 3)) == "#" * 24
    assert ma.text_bar(40, 40, 1) == ""


def test_exaggeration_always_small_limit():
    checked, failures = ma.exaggeration_always(20)
    assert checked == sum((a - 1) * (a - 2) // 2 for a in range(1, 21))
    assert failures == []


def test_zero_axis_is_honest():
    for a in range(2, 30):
        for c in range(1, a):
            assert ma.apparent_ratio(a, c, 0) == Fraction(a, c)
