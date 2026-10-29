import math

import congruences_fermat_test as cf


def test_primes_and_phi():
    assert [n for n in range(20) if cf.is_prime(n)] == [2, 3, 5, 7, 11, 13, 17, 19]
    assert [cf.phi(n) for n in range(1, 13)] == [1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4]
    assert cf.phi(561) == 2 * 10 * 16


def test_fermat_euler_hold_and_fail_where_expected():
    assert all(cf.fermat_holds(p) for p in (2, 3, 5, 97, 101))
    assert not cf.fermat_holds(15)
    assert all(cf.euler_holds(n) for n in (1, 2, 12, 100, 561))


def test_wilson_characterises_primes():
    for n in range(2, 120):
        assert (cf.wilson_residue(n) == n - 1) == cf.is_prime(n)
    assert cf.wilson_residue(4) == 2  # the one composite where (n-1)! is not 0
    assert all(cf.wilson_residue(n) == 0 for n in range(6, 60) if not cf.is_prime(n))


def test_pseudoprimes_and_liars():
    psp = cf.pseudoprimes_base2(2000)
    assert psp == [341, 561, 645, 1105, 1387, 1729, 1905]
    assert 3 not in cf.fermat_liar_bases(341)
    assert len(cf.fermat_liar_bases(561)) == cf.phi(561)


def test_carmichael_numbers_and_korselt():
    carm = cf.carmichael_numbers(10_000)
    assert carm == [561, 1105, 1729, 2465, 2821, 6601, 8911]
    korselt = [n for n in range(3, 3000, 2) if cf.korselt(n)]
    assert korselt == [561, 1105, 1729, 2465, 2821]
    assert all(math.gcd(n, 2) == 1 for n in carm)
