import math
import random

import pytest

import cryptography_rsa_toy as rt


@pytest.mark.parametrize("b,e,n", [(2, 10, 1000), (3, 0, 7), (5, 117, 19), (0, 5, 13), (7, 1, 1), (123, 456, 789)])
def test_pow_mod_matches_builtin(b, e, n):
    value, mults = rt.pow_mod(b, e, n)
    assert value == pow(b, e, n)
    assert mults <= 2 * max(e.bit_length(), 1)


def test_pow_mod_multiplication_count():
    # 65537 = 2^16 + 1: 16 squarings and 2 multiplications into the result.
    assert rt.pow_mod(3, 65537, 10**9 + 7)[1] == 18


def test_miller_rabin_on_known_numbers():
    rng = random.Random(1)
    primes = [2, 3, 5, 7, 97, 7919, 1_000_003, 2_147_483_647]
    composites = [1, 4, 9, 91, 561, 1105, 1729, 2047, 3215031751, 2_147_483_649]
    assert all(rt.is_probable_prime(p, rng) for p in primes)
    assert not any(rt.is_probable_prime(c, rng) for c in composites)


def test_key_generation_and_round_trip():
    rng = random.Random(7)
    n, e, d, p, q = rt.make_key(16, rng)
    assert n == p * q and p != q
    assert p.bit_length() == q.bit_length() == 16
    assert e * d % ((p - 1) * (q - 1)) == 1
    for m in [0, 1, 2, p, q, n - 1, 12345]:
        c, _ = rt.pow_mod(m, e, n)
        assert rt.pow_mod(c, d, n)[0] == m % n  # works even when gcd(m, n) > 1


def test_trial_division_breaks_small_keys():
    rng = random.Random(3)
    n, e, d, p, q = rt.make_key(14, rng)
    f = rt.smallest_factor(n)
    assert f in (p, q) and n % f == 0
    assert pow(e, -1, (f - 1) * (n // f - 1)) == d
    assert rt.smallest_factor(97) == 97
    assert math.gcd(e, (p - 1) * (q - 1)) == 1
