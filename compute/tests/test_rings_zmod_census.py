from itertools import combinations
from math import gcd

import pytest

import rings_zmod_census as rz


@pytest.mark.parametrize("n", [2, 6, 8, 12, 13, 30])
def test_units_are_the_coprime_residues(n):
    assert rz.units(n) == [a for a in range(n) if gcd(a, n) == 1]


def test_zero_divisors_examples():
    assert rz.zero_divisors(6) == [2, 3, 4]
    assert rz.zero_divisors(7) == []
    assert rz.zero_divisors(8) == [2, 4, 6]


def test_nilpotents_and_idempotents():
    assert rz.nilpotents(8) == [0, 2, 4, 6]
    assert rz.nilpotents(12) == [0, 6]
    assert rz.idempotents(6) == [0, 1, 3, 4]
    assert rz.idempotents(9) == [0, 1]


@pytest.mark.parametrize("n", [2, 3, 4, 6, 8, 9, 10])
def test_ideals_complete_against_all_subsets(n):
    brute = sorted((tuple(sorted(c)) for k in range(1, n + 1)
                    for c in combinations(range(n), k) if rz.is_ideal(c, n)), key=len)
    assert sorted(rz.ideals(n)) == sorted(brute)


def test_ideals_match_divisors():
    for n in range(2, 40):
        sizes = sorted(len(i) for i in rz.ideals(n))
        assert sizes == sorted(n // d for d in range(1, n + 1) if n % d == 0)


def test_domain_iff_field_iff_prime():
    for n in range(2, 50):
        domain = not rz.zero_divisors(n)
        field = len(rz.units(n)) == n - 1
        assert domain == field == rz.is_prime(n)
