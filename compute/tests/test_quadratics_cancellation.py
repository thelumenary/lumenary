import math
from decimal import Decimal

import pytest

import quadratics_cancellation as qc


def test_stable_roots_satisfy_vieta_and_equation():
    big, small = qc.stable_roots(1.0, -5.0, 6.0)
    assert {round(big, 12), round(small, 12)} == {3.0, 2.0}
    assert math.isclose(big * small, 6.0)
    big, small = qc.stable_roots(2.0, 3.0, -2.0)
    assert {round(big, 12), round(small, 12)} == {-2.0, 0.5}
    with pytest.raises(ValueError):
        qc.stable_roots(1.0, 0.0, 1.0)


def test_reference_value_is_accurate():
    ref = qc.reference_small_root(10 ** 8)
    # small root = 1/B + 1/B^3 + 2/B^5 + ... for x^2 - Bx + 1
    approx = Decimal(1) / 10 ** 8 + Decimal(1) / 10 ** 24
    assert abs(ref - approx) < Decimal("1e-39")


def test_naive_formula_loses_accuracy_but_vieta_does_not():
    exact = qc.reference_small_root(10 ** 8)
    naive = qc.naive_small_root(1.0, -1e8, 1.0)
    vieta = qc.stable_roots(1.0, -1e8, 1.0)[1]
    assert qc.relative_error(naive, exact) > 0.1
    assert qc.relative_error(vieta, exact) < 1e-15


def test_both_methods_agree_for_moderate_coefficients():
    exact = qc.reference_small_root(100)
    assert qc.relative_error(qc.naive_small_root(1.0, -100.0, 1.0), exact) < 1e-12
    assert qc.relative_error(qc.stable_roots(1.0, -100.0, 1.0)[1], exact) < 1e-15
