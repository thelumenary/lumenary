import math

import pytest

import markov_chains_polya_walks as ex


def test_return_probs_1d_are_central_binomials():
    a = ex.return_probs_1d(20)
    for n in range(21):
        assert a[n] == pytest.approx(math.comb(2 * n, n) / 4 ** n)


def test_central_binomial_bounds_used_in_lean():
    a = ex.return_probs_1d(500)
    assert all(a[n] >= 1 / (2 * n + 1) for n in range(501))
    assert all(4 * n * a[n] ** 2 >= 1 - 1e-12 for n in range(1, 501))


def test_return_prob_3d_small_cases():
    # n = 1: the walk must step and step back along the same axis: 6 * (1/6)^2.
    assert ex.return_prob_3d(1) == pytest.approx(1 / 6)
    # n = 2 by brute force over the 6^4 four-step walks.
    steps = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
    count = 0
    for s1 in steps:
        for s2 in steps:
            for s3 in steps:
                for s4 in steps:
                    if all(sum(v) == 0 for v in zip(s1, s2, s3, s4)):
                        count += 1
    assert ex.return_prob_3d(2) == pytest.approx(count / 6 ** 4)


def test_3d_asymptotics():
    n = 60
    ratio = ex.return_prob_3d(n) / (2 * (3 / (4 * math.pi * n)) ** 1.5)
    assert ratio == pytest.approx(1.0, abs=0.05)


def test_simulation_orders_dimensions():
    f1, f2, f3 = (ex.simulate_returns(d, walks=400, steps=400) for d in (1, 2, 3))
    assert f1 > f2 > f3
    assert f1 > 0.9 and f3 < 0.45
    assert ex.simulate_returns(2, walks=50, steps=50) == ex.simulate_returns(2, walks=50, steps=50)
