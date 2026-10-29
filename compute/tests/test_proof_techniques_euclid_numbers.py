from math import prod

import pytest

import proof_techniques_euclid_numbers as en


def test_first_primes():
    assert en.first_primes(0) == []
    assert en.first_primes(10) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


def test_factorize():
    assert en.factorize(2) == [2]
    assert en.factorize(360) == [2, 2, 2, 3, 3, 5]
    assert en.factorize(30031) == [59, 509]
    assert en.factorize(510511) == [19, 97, 277]
    for n in range(2, 500):
        fs = en.factorize(n)
        assert prod(fs) == n and fs == sorted(fs)
    with pytest.raises(ValueError):
        en.factorize(1)


def test_euclid_numbers_have_only_new_prime_factors():
    for k in range(1, 10):
        ps = en.first_primes(k)
        n = en.euclid_number(ps)
        assert all(f not in ps for f in en.factorize(n))
    assert en.euclid_number(en.first_primes(6)) == 30031


def test_running_check_finds_true_and_false_formulas():
    assert en.running_check(lambda i: i, lambda n: n * (n - 1) // 2, 2000) is None
    assert en.running_check(lambda i: 2 * i + 1, lambda n: n * n, 2000) is None
    # A wrong closed form is caught at the first n where it disagrees.
    assert en.running_check(lambda i: i, lambda n: n * (n - 1) // 2 + (n >= 5), 100) == 5


def test_fake_theorem():
    assert all(en.step_difference(n) == 2 * (n + 1) for n in range(1000))
    assert en.first_failure(lambda n: (n * n + n + 1) % 2 == 0, 100) == 0
    assert en.first_failure(lambda n: n < 7, 100) == 7
    assert en.first_failure(lambda n: True, 50) is None
