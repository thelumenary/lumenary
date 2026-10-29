import math
import random

import pytest

import stochastic_processes_poisson_process as pp


def test_pmf_values_and_normalisation():
    assert pp.poisson_pmf(0.0, 0) == 1.0
    assert pp.poisson_pmf(2.0, 1) == pytest.approx(2 * math.exp(-2))
    assert math.fsum(pp.poisson_pmf(6.0, k) for k in range(80)) == pytest.approx(1.0)
    with pytest.raises(ValueError):
        pp.poisson_pmf(-1.0, 2)


def test_convolution_identity():
    for s, t in [(0.5, 0.5), (1.3, 2.4), (5.0, 0.1)]:
        assert max(pp.convolution_gap(s, t, k) for k in range(25)) < 1e-14


def test_arrivals_sorted_and_in_range():
    times = pp.arrival_times(3.0, 10.0, random.Random(4))
    assert times == sorted(times)
    assert all(0 < t <= 10.0 for t in times)
    assert pp.count_in(times, 0.0, 10.0) == len(times)
    assert pp.count_in([0.5, 1.0, 1.5], 0.5, 1.5) == 2  # half-open (a, b]


def test_counts_have_poisson_mean_and_variance():
    rng = random.Random(11)
    counts = [len(pp.arrival_times(2.0, 3.0, rng)) for _ in range(4000)]
    mean = sum(counts) / len(counts)
    var = sum((c - mean) ** 2 for c in counts) / len(counts)
    assert abs(mean - 6) < 0.2
    assert abs(var - 6) < 0.5
