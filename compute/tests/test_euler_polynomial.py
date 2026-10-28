import pytest

import euler_polynomial as ep

SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def test_is_prime_small_numbers():
    assert [n for n in range(50) if ep.is_prime(n)] == SMALL_PRIMES


@pytest.mark.parametrize("n", [-7, -1, 0, 1, 4, 9, 15, 25, 49, 1681, 1763, 7919 * 7919])
def test_is_prime_rejects_non_primes(n):
    assert not ep.is_prime(n)


@pytest.mark.parametrize("n", [2, 7919, 104729, 1000003])
def test_is_prime_accepts_primes(n):
    assert ep.is_prime(n)


@pytest.mark.parametrize("n,f", [(2, 2), (9, 3), (1681, 41), (1763, 41), (97, 97), (91, 7)])
def test_smallest_factor(n, f):
    assert ep.smallest_factor(n) == f


def test_smallest_factor_rejects_small_input():
    with pytest.raises(ValueError):
        ep.smallest_factor(1)


def test_euler_values():
    assert ep.euler(0) == 41
    assert ep.euler(39) == 1601
    assert ep.euler(40) == 1681 == 41 * 41


@pytest.mark.parametrize("n", range(40))
def test_euler_prime_for_first_forty(n):
    assert ep.is_prime(ep.euler(n))


def test_first_failure_is_forty():
    assert ep.first_failure(ep.euler) == 40
    assert ep.first_failure(ep.euler, start=41) == 41
    assert ep.first_failure(ep.euler, stop=40) is None


def test_first_failure_for_other_polynomials():
    assert ep.first_failure(lambda n: n) == 0
    assert ep.first_failure(lambda n: 2 * n + 1, start=1) == 4  # 9


def test_prime_counts():
    assert ep.prime_count(ep.euler, 40) == 40
    assert ep.prime_count(ep.euler, 100) == 86
    assert ep.prime_count(ep.euler, 1000) == 581
    assert ep.prime_count(ep.euler, 0) == 0


def test_every_n_divisible_by_41_from_40_is_composite():
    # p(41k) and p(41k - 1) are divisible by 41, so the pattern fails infinitely often.
    for k in range(1, 20):
        assert ep.euler(41 * k) % 41 == 0 and ep.euler(41 * k - 1) % 41 == 0
        assert not ep.is_prime(ep.euler(41 * k))
