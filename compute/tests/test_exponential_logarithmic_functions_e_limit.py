import math
from fractions import Fraction

import pytest

import exponential_logarithmic_functions_e_limit as el


def test_compound_small_cases_exact():
    assert el.compound_exact(1) == 2
    assert el.compound_exact(2) == Fraction(9, 4)
    assert math.isclose(el.compound(12), float(el.compound_exact(12)), rel_tol=1e-14)


def test_compound_increases_towards_e():
    values = [el.compound(n) for n in [1, 2, 5, 10, 100, 1000]]
    assert all(a < b for a, b in zip(values, values[1:]))
    assert all(v < math.e for v in values)
    assert values[0] >= 2


def test_error_is_about_e_over_2n():
    for n in [10 ** 3, 10 ** 5]:
        err = math.e - el.compound(n)
        assert abs(n * err - math.e / 2) < 2 / n + 1e-6


def test_series_partial_sums():
    assert el.series_partial_sum(1) == 1
    assert el.series_partial_sum(3) == Fraction(5, 2)
    assert el.series_partial_sum(5) == Fraction(65, 24)
    assert abs(float(el.series_partial_sum(18)) - math.e) < 1e-15


def test_compound_rejects_bad_n():
    with pytest.raises(ValueError):
        el.compound(0)
