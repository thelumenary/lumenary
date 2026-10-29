import math
from fractions import Fraction

import pytest

import quadratics_discriminant as qd


def test_discriminant_and_classification():
    assert qd.discriminant(1, -5, 6) == 1
    assert qd.classify(1, -5, 6) == "two"
    assert qd.classify(1, 2, 1) == "one"
    assert qd.classify(1, 0, 1) == "none"
    with pytest.raises(ValueError):
        qd.classify(0, 1, 1)


def test_rational_roots_are_exact_roots():
    assert qd.rational_roots(1, -5, 6) == [2, 3]
    assert qd.rational_roots(2, -3, -2) == [Fraction(-1, 2), 2]
    assert qd.rational_roots(1, 2, 1) == [-1]
    assert qd.rational_roots(1, 0, -2) is None  # sqrt(8) is irrational
    assert qd.rational_roots(1, 0, 1) is None


def test_census_totals_and_no_failures():
    counts = qd.census()
    assert counts["two"] + counts["one"] + counts["none"] == 10 * 11 * 11
    assert counts["failures"] == 0
    assert counts == {"two": 730, "one": 26, "none": 454, "rational": 276, "failures": 0}
    small = qd.census(1)
    assert small["two"] + small["one"] + small["none"] == 2 * 3 * 3


def test_census_symmetry():
    # Replacing (a, b, c) by (-a, -b, -c) keeps the discriminant, so in the
    # census the cases a > 0 and a < 0 are equally common; in particular the
    # number of 'one' cases is even.
    assert qd.census()["one"] % 2 == 0


def test_simulation_close_to_exact_value():
    assert abs(qd.EXACT_PROBABILITY - 0.6272067) < 1e-6
    p = qd.simulate(20000)
    se = math.sqrt(p * (1 - p) / 20000)
    assert abs(p - qd.EXACT_PROBABILITY) < 4 * se
    assert qd.simulate(1000, seed=1) == qd.simulate(1000, seed=1)
