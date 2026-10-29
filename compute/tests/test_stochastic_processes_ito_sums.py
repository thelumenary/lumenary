import math
import random

import pytest

import stochastic_processes_ito_sums as its


def test_path_shape_and_start():
    path = its.brownian_path(6, random.Random(1))
    assert len(path) == 65 and path[0] == 0.0
    assert its.subsample(path, 16) == path[::16]
    assert len(its.subsample(path, 16)) == 5


def test_discrete_ito_and_stratonovich_identities_hold_for_any_path():
    rng = random.Random(2)
    for _ in range(20):
        path = [rng.uniform(-3, 3) for _ in range(rng.randint(2, 40))]
        a, b = path[0], path[-1]
        assert its.stratonovich_sum(path) == pytest.approx((b * b - a * a) / 2)
        assert its.ito_sum(path) == pytest.approx(
            (b * b - a * a) / 2 - its.quadratic_variation(path) / 2)


def test_random_walk_quadratic_variation_is_n():
    rng = random.Random(3)
    walk = [0]
    for _ in range(100):
        walk.append(walk[-1] + rng.choice([-1, 1]))
    assert its.quadratic_variation(walk) == 100
    assert its.ito_sum(walk) == (walk[-1] ** 2 - 100) / 2
    assert its.total_variation(walk) == 100


def test_brownian_quadratic_variation_close_to_one():
    qv = [its.quadratic_variation(its.brownian_path(14, random.Random(s)))
          for s in range(5)]
    # QV of n Gaussian increments with variance 1/n has sd sqrt(2/n) ~ 0.011
    assert all(abs(q - 1) < 0.06 for q in qv)
    tv = its.total_variation(its.brownian_path(14, random.Random(9)))
    assert abs(tv - math.sqrt(2 * 2 ** 14 / math.pi)) < 5
