import math
import random

import cryptography_discrete_log as dl


def test_generators():
    assert dl.prime_factors(360) == [2, 3, 5]
    assert dl.prime_factors(97) == [97]
    assert dl.smallest_generator(7) == 3
    assert dl.smallest_generator(101) == 2
    assert dl.smallest_generator(2_147_483_647) == 7
    for p in (11, 13, 101):
        for g in range(2, p):
            orbit = {pow(g, k, p) for k in range(p - 1)}
            assert dl.is_generator(g, p) == (len(orbit) == p - 1)


def test_diffie_hellman_agreement():
    rng = random.Random(0)
    p, g = 1_000_000_007, dl.smallest_generator(1_000_000_007)
    for _ in range(20):
        a, b = rng.randrange(2, p - 1), rng.randrange(2, p - 1)
        assert pow(pow(g, b, p), a, p) == pow(pow(g, a, p), b, p)


def test_logs_are_found_and_agree():
    rng = random.Random(5)
    for p in (101, 1009, 7919):
        g = dl.smallest_generator(p)
        for _ in range(10):
            x = rng.randrange(0, p - 1)
            h = pow(g, x, p)
            assert dl.brute_force_log(g, h, p)[0] == x
            assert dl.bsgs_log(g, h, p)[0] == x


def test_step_counts():
    p = 100_003
    g = dl.smallest_generator(p)
    x, steps = dl.brute_force_log(g, pow(g, 500, p), p)
    assert (x, steps) == (500, 501)
    worst = max(dl.bsgs_log(g, pow(g, x, p), p)[1] for x in range(0, p - 1, 997))
    assert worst <= 2 * (math.isqrt(p - 1) + 1)
