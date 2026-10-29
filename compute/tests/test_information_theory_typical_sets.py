import math

import pytest

import information_theory_typical_sets as ex


def test_h2():
    assert ex.h2(0.5) == pytest.approx(1.0)
    assert ex.h2(0.2) == pytest.approx(0.7219, abs=1e-4)


def test_log2_comb():
    assert ex.log2_comb(10, 3) == pytest.approx(math.log2(120))
    assert ex.log2_comb(5, 0) == pytest.approx(0.0, abs=1e-12)


def test_typical_set_with_huge_eps_is_everything():
    prob, log_size = ex.typical_set(12, 0.2, 10.0)
    assert prob == pytest.approx(1.0)
    assert log_size == pytest.approx(12.0)


def test_typical_probability_increases_and_size_bounded():
    p, eps = 0.2, 0.05
    h = ex.h2(p)
    probs = []
    for n in [100, 500, 1000, 2000]:
        prob, log_size = ex.typical_set(n, p, eps)
        probs.append(prob)
        assert log_size <= n * (h + eps) + 1e-9
    assert probs == sorted(probs)
    assert probs[-1] > 0.99


def test_lower_bound_once_probable():
    n, p, eps = 2000, 0.2, 0.05
    prob, log_size = ex.typical_set(n, p, eps)
    assert log_size >= n * (ex.h2(p) - eps) + math.log2(prob)
