import math

import computational_reproducibility_seeds as cs


def test_fnv1a64_test_vectors():
    assert cs.fnv1a64("") == 0xCBF29CE484222325
    assert cs.fnv1a64("a") == 0xAF63DC4C8601EC8C
    assert cs.fnv1a64("foobar") == 0x85944171F73967E8
    assert cs.fnv1a64("0.1") != cs.fnv1a64("0.10")


def test_minstd_known_value():
    # Park and Miller (1988): from seed 1, the 10,000th output is 1043618065
    assert cs.minstd(1, 10_000)[-1] == 1043618065
    assert cs.minstd(42, 3) == cs.minstd(42, 3)


def test_true_value():
    # integral of exp(-x^2) on [0, 1] by a fine midpoint rule
    n = 20000
    mid = sum(math.exp(-((k + 0.5) / n) ** 2) for k in range(n)) / n
    assert abs(mid - cs.TRUE_VALUE) < 1e-9


def test_same_seed_same_result_different_seed_different_result():
    assert cs.monte_carlo(7, 500) == cs.monte_carlo(7, 500)
    assert cs.monte_carlo(7, 500) != cs.monte_carlo(8, 500)


def test_estimates_are_statistically_sensible():
    mean, se = cs.monte_carlo(11, 20000)
    assert 0 < se < 0.01
    assert abs(mean - cs.TRUE_VALUE) < 5 * se
    hits = cs.coverage(range(100, 300), 1000)
    assert 170 <= hits <= 200
