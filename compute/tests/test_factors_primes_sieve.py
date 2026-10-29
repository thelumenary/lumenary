import math

import pytest

import factors_primes_sieve as fps


def test_sieve_small_values():
    assert fps.sieve(1) == []
    assert fps.sieve(2) == [2]
    assert fps.sieve(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert len(fps.sieve(100)) == 25
    assert len(fps.sieve(1000)) == 168


def test_stopping_at_square_root_is_enough_but_earlier_is_not():
    for n in [10, 50, 100, 500, 1000]:
        assert fps.sieve(n, stop_at=math.isqrt(n)) == fps.sieve(n)
    # Stopping before 7 leaves 49 = 7 x 7 uncrossed.
    assert 49 in fps.sieve(100, stop_at=6)


def test_smallest_factor_is_prime():
    primes = set(fps.sieve(2000))
    for n in range(2, 2000):
        p = fps.smallest_factor(n)
        assert n % p == 0 and p in primes
    with pytest.raises(ValueError):
        fps.smallest_factor(1)


def test_factor_trees_multiply_back_and_agree():
    assert fps.tree_small_first(360) == [2, 2, 2, 3, 3, 5]
    assert fps.tree_middle_split(360) == [2, 2, 2, 3, 3, 5]
    assert fps.tree_small_first(97) == [97]
    assert fps.tree_middle_split(1) == []
    primes = set(fps.sieve(3000))
    for n in range(2, 3000):
        leaves = fps.tree_middle_split(n)
        assert math.prod(leaves) == n
        assert all(p in primes for p in leaves)
        assert leaves == fps.tree_small_first(n)


def test_euclid_numbers_have_new_prime_factors():
    rows = fps.euclid_numbers(7)
    assert rows[5][1] == 30031 and rows[5][2] == [59, 509]
    assert rows[6][2] == [19, 97, 277]
    for used, number, factors in rows:
        assert math.prod(factors) == number
        assert not set(factors) & set(used)
