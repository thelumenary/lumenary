from fractions import Fraction

import numpy as np
import pytest

import markov_chains_convergence as ex


def test_weather_chain_is_stochastic():
    assert ex.is_stochastic(ex.as_fractions(ex.WEATHER))
    assert not ex.is_stochastic([[Fraction(1, 2), Fraction(1, 3)], [0, 1]])


def test_stationary_exact_weather():
    pi = ex.stationary_exact(ex.WEATHER)
    assert pi == [Fraction(7, 18), Fraction(1, 3), Fraction(5, 18)]
    p = ex.as_fractions(ex.WEATHER)
    assert [sum(pi[i] * p[i][j] for i in range(3)) for j in range(3)] == pi


def test_stationary_two_state_formula():
    a, b = Fraction(1, 5), Fraction(1, 2)
    pi = ex.stationary_exact([[1 - a, a], [b, 1 - b]])
    assert pi == [b / (a + b), a / (a + b)]


def test_tv_distance():
    assert ex.tv_distance([1, 0], [0, 1]) == 1.0
    assert ex.tv_distance([0.5, 0.5], [0.5, 0.5]) == 0.0


def test_distances_decay_below_doeblin_bound():
    tv = ex.distances(ex.WEATHER, 0, 12)
    assert tv[0] == pytest.approx(11 / 18)
    assert all(tv[n] <= 0.7 ** n + 1e-12 for n in range(13))
    assert all(a > b for a, b in zip(tv, tv[1:]))


def test_second_eigenvalue_and_rate():
    lam2 = ex.second_eigenvalue(ex.WEATHER)
    assert lam2 == pytest.approx(0.4)
    tv = ex.distances(ex.WEATHER, 2, 20)
    assert tv[20] / tv[19] == pytest.approx(lam2, rel=1e-3)


def test_periodic_chain_does_not_converge():
    tv = ex.distances([[0, 1], [1, 0]], 0, 6)
    assert all(d == pytest.approx(0.5) for d in tv)
