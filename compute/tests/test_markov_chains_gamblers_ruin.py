import random
from fractions import Fraction

import pytest

import markov_chains_gamblers_ruin as ex


def test_solve_tridiagonal_small_system():
    # [[2, 1, 0], [1, 2, 1], [0, 1, 2]] x = [3, 4, 3]  ->  x = [1, 1, 1]
    x = ex.solve_tridiagonal([0, 1, 1], [Fraction(2)] * 3, [1, 1, 0], [3, 4, 3])
    assert x == [1, 1, 1]


@pytest.mark.parametrize("p", [Fraction(1, 2), Fraction(18, 38), Fraction(3, 5)])
def test_first_step_matches_formula(p):
    h = ex.first_step(p, 12)
    assert h[0] == 0 and h[12] == 1
    assert all(h[i] == ex.ruin_formula(p, i, 12) for i in range(13))
    q = 1 - p
    assert all(h[i] == p * h[i + 1] + q * h[i - 1] for i in range(1, 12))


def test_fair_durations():
    m = ex.first_step(Fraction(1, 2), 20, durations=True)
    assert all(m[i] == i * (20 - i) for i in range(21))


def test_biased_durations_satisfy_equations():
    p = Fraction(18, 38)
    m = ex.first_step(p, 20, durations=True)
    assert m[0] == m[20] == 0
    assert all(m[i] == 1 + p * m[i + 1] + (1 - p) * m[i - 1] for i in range(1, 20))


def test_ruin_formula_values():
    assert ex.ruin_formula(Fraction(1, 2), 3, 10) == Fraction(3, 10)
    r = Fraction(10, 9)
    assert ex.ruin_formula(Fraction(18, 38), 10, 20) == 1 / (1 + r ** 10)


def test_simulation_is_close_and_reproducible():
    rng1, rng2 = random.Random(5), random.Random(5)
    assert ex.simulate(0.5, 3, 6, 200, rng1) == ex.simulate(0.5, 3, 6, 200, rng2)
    frac, mean = ex.simulate(0.5, 5, 10, 3000, random.Random(11))
    assert abs(frac - 0.5) < 0.04
    assert abs(mean - 25) < 2.5
