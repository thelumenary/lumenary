import statistics
from fractions import Fraction

import pytest

import statistics_intro_outliers as so


def test_class_a_summary():
    s = so.summary(so.CLASS_A)
    assert s["mean"] == Fraction(257, 15)
    assert s["median"] == 15
    assert s["modes"] == [12]
    assert s["range"] == 40
    assert (s["Q1"], s["Q3"], s["IQR"]) == (10, 20, 10)
    assert so.outliers(so.CLASS_A) == [45]


def test_median_even_and_odd_and_unsorted():
    assert so.median([3, 1, 2]) == 2
    assert so.median([4, 1, 3, 2]) == Fraction(5, 2)
    with pytest.raises(ValueError):
        so.median([])


def test_quartile_convention_excludes_median():
    assert so.quartiles([1, 2, 3, 4, 5, 6, 7]) == (2, 6)
    assert so.quartiles([1, 2, 3, 4, 5, 6, 7, 8]) == (Fraction(5, 2), Fraction(13, 2))


def test_mean_matches_statistics_module():
    for data in (so.CLASS_A, so.ROUTE_1, so.ROUTE_2):
        assert so.mean(data) == statistics.mean(Fraction(v) for v in data)


def test_median_resists_but_mean_does_not():
    base = so.summary(so.CLASS_A)
    for big in (90, 180, 900, 10**6):
        t = so.summary(so.CLASS_A[:-1] + [big])
        assert t["median"] == base["median"]
        assert t["IQR"] == base["IQR"]
        # The mean moves by (change)/n.
        assert t["mean"] - base["mean"] == Fraction(big - 45, 15)


def test_same_mean_different_spread():
    r1, r2 = so.summary(so.ROUTE_1), so.summary(so.ROUTE_2)
    assert r1["mean"] == r2["mean"] == 10
    assert r1["range"] == 2 and r2["range"] == 18
    assert r1["IQR"] < r2["IQR"]
