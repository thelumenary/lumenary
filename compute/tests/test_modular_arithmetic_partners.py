import math

import pytest

import modular_arithmetic_partners as mp


def test_partners_known_moduli():
    assert mp.partners(10) == [1, 3, 7, 9]
    assert mp.partners(12) == [1, 5, 7, 11]
    assert mp.partners(7) == [1, 2, 3, 4, 5, 6]
    assert mp.partners(1) == []
    with pytest.raises(ValueError):
        mp.partners(0)


def test_partner_of_values_and_none():
    assert mp.partner_of(3, 11) == 4
    assert mp.partner_of(7, 10) == 3
    assert mp.partner_of(4, 10) is None
    assert mp.partner_of(0, 13) is None
    for n in range(2, 25):
        for a in mp.partners(n):
            assert a * mp.partner_of(a, n) % n == 1


def test_partners_are_coprime_remainders():
    for n in range(2, 41):
        assert mp.partners(n) == mp.coprime_remainders(n)
        assert all(math.gcd(a, n) == 1 for a in mp.partners(n))


def test_zero_products():
    assert mp.zero_products(7) == []
    assert (3, 4) in mp.zero_products(12) and (4, 3) in mp.zero_products(12)
    assert (2, 5) in mp.zero_products(10)
    for n in range(2, 40):
        assert (mp.zero_products(n) == []) == mp.is_prime(n)


def test_reduce_first_rules_hold():
    cases, failures = mp.reduce_first_failures(12, 40)
    assert cases == 12 * 40 * 40
    assert failures == 0


def test_is_prime_small_values():
    assert [n for n in range(2, 30) if mp.is_prime(n)] == [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert not mp.is_prime(1) and not mp.is_prime(0)
