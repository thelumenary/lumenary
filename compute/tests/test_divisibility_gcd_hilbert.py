import math
from math import gcd

import divisibility_gcd_hilbert as dh


def test_hilbert_irreducibles():
    irr = dh.hilbert_irreducibles(100)
    assert irr[:6] == [5, 9, 13, 17, 21, 29]
    assert 25 not in irr and 45 not in irr and 49 in irr
    assert all(n % 4 == 1 for n in irr)


def test_non_unique_factorisations():
    irr = dh.hilbert_irreducibles(1500)
    assert sorted(dh.factorizations(441, irr)) == [(9, 49), (21, 21)]
    multi = [n for n in range(1, 1501, 4) if len(dh.factorizations(n, irr)) > 1]
    assert multi == [441, 693, 1089, 1197, 1449]
    # every Hilbert number has at least one factorisation into irreducibles
    assert all(dh.factorizations(n, irr) for n in range(1, 1501, 4))


def test_unique_prime_factorisation_in_range():
    primes = dh.primes_up_to(1000)
    assert primes[:8] == [2, 3, 5, 7, 11, 13, 17, 19]
    assert len(primes) == 168
    for n in range(2, 1001):
        fs = dh.factorizations(n, primes)
        assert len(fs) == 1 and math.prod(fs[0]) == n


def test_totients_and_coprime_pairs():
    phi = dh.totients(200)
    assert phi[1:11] == [1, 1, 2, 2, 4, 2, 6, 4, 6, 4]
    for n in (1, 7, 30, 60):
        brute = sum(1 for a in range(1, n + 1) for b in range(1, n + 1) if gcd(a, b) == 1)
        assert dh.coprime_pairs(n, phi) == brute


def test_coprime_density_near_six_over_pi_squared():
    phi = dh.totients(20_000)
    ratio = dh.coprime_pairs(20_000, phi) / 20_000 ** 2
    assert abs(ratio - 6 / math.pi ** 2) < 1e-3
