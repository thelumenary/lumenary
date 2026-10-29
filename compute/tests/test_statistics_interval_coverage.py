import math

import pytest

import statistics_interval_coverage as ex


def test_binomial_pmf_sums_to_one_and_matches_comb():
    assert sum(ex.binomial_pmf(20, k, 0.3) for k in range(21)) == pytest.approx(1.0)
    assert ex.binomial_pmf(10, 3, 0.5) == pytest.approx(math.comb(10, 3) / 1024)
    assert ex.binomial_pmf(5, 0, 0.0) == 1.0
    assert ex.binomial_pmf(5, 5, 1.0) == 1.0


def test_wald_interval_degenerates_at_zero():
    # With k = 0 the Wald interval is the single point 0: it never covers p > 0.
    assert ex.wald_interval(0, 10) == (0.0, 0.0)
    low, high = ex.wald_interval(50, 100)
    assert (low + high) / 2 == pytest.approx(0.5)
    assert high - low == pytest.approx(2 * ex.Z * 0.05)


def test_wilson_interval_is_inside_unit_interval_and_never_empty():
    for n in [5, 30]:
        for k in range(n + 1):
            low, high = ex.wilson_interval(k, n)
            assert -1e-12 <= low < high <= 1 + 1e-12


def test_coverage_values():
    # n = 10, p = 0.05: Wald covers only when k = 1, 2, 3 (k = 0 gives {0};
    # for k = 4 the lower end 0.4 - 1.96 sqrt(0.024) is about 0.096 > 0.05).
    expected = sum(ex.binomial_pmf(10, k, 0.05) for k in (1, 2, 3))
    assert ex.coverage(ex.wald_interval, 10, 0.05) == pytest.approx(expected)
    assert ex.coverage(ex.wald_interval, 10, 0.05) < 0.5
    assert ex.coverage(ex.wilson_interval, 1000, 0.5) == pytest.approx(0.95, abs=0.01)


def test_large_n_wald_is_close_to_nominal():
    assert abs(ex.coverage(ex.wald_interval, 1000, 0.2) - 0.95) < 0.01


def test_simulation_is_deterministic_and_ordered():
    a = ex.simulate_normal_intervals(reps=1000, seed=7)
    b = ex.simulate_normal_intervals(reps=1000, seed=7)
    assert a == b
    known, t_int, naive = ex.simulate_normal_intervals()
    assert abs(known - 0.95) < 0.02 and abs(t_int - 0.95) < 0.02
    assert naive < 0.91  # true coverage of the naive interval is about 0.88
    assert naive < t_int
