import math
import random
import statistics

import pytest

import vectors_random_angles as ra


def test_cos_angle_known_values():
    assert ra.cos_angle([1, 0], [0, 1]) == pytest.approx(0)
    assert ra.cos_angle([1, 0], [1, 1]) == pytest.approx(math.sqrt(2) / 2)
    assert ra.cos_angle([2, 0, 0], [-5, 0, 0]) == pytest.approx(-1)
    assert ra.cos_angle([1, 2, 2], [2, -1, 2]) == pytest.approx(4 / 9)


def test_cos_angle_is_scale_invariant_and_bounded():
    rng = random.Random(5)
    for _ in range(100):
        u, v = ra.random_vector(4, rng), ra.random_vector(4, rng)
        c = ra.cos_angle(u, v)
        assert -1 <= c <= 1
        assert ra.cos_angle([3 * a for a in u], [0.5 * b for b in v]) == pytest.approx(c)


def test_sampling_is_seeded():
    a = ra.sample_cosines(5, 20, random.Random(1))
    b = ra.sample_cosines(5, 20, random.Random(1))
    assert a == b and len(a) == 20


def test_spread_shrinks_like_one_over_root_n():
    rng = random.Random(11)
    for n in (4, 50, 400):
        sd = statistics.pstdev(ra.sample_cosines(n, 400, rng))
        assert sd == pytest.approx(1 / math.sqrt(n), rel=0.15)


def test_mean_cosine_near_zero():
    rng = random.Random(3)
    cosines = ra.sample_cosines(200, 500, rng)
    assert abs(statistics.mean(cosines)) < 0.02
