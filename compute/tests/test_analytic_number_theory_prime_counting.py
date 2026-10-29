import math

import pytest

import analytic_number_theory_prime_counting as pc


@pytest.fixture(scope="module")
def flags():
    return pc.sieve(100000)


def test_sieve_small():
    f = pc.sieve(30)
    assert [k for k in range(31) if f[k]] == [2, 3, 5, 7, 11, 13, 17, 19,
                                              23, 29]
    assert pc.sieve(1)[0] == 0 and pc.sieve(1)[1] == 0


def test_known_prime_counts(flags):
    assert pc.prime_counts(flags, [10, 100, 1000, 10000, 100000]) == [
        4, 25, 168, 1229, 9592]


def test_li_values():
    assert abs(pc.li(10) - 6.1655995) < 1e-6
    assert abs(pc.li(1000) - 177.6096580) < 1e-6
    assert abs(pc.li(2) - 1.0451638) < 1e-6


def test_psi_small_values(flags):
    # psi(10) = 3 log 2 + 2 log 3 + log 5 + log 7 = log 2520 = log lcm(1..10)
    assert abs(pc.psi(flags, 10) - math.log(2520)) < 1e-12
    assert abs(pc.psi(flags, 30) - math.log(2329089562800)) < 1e-9


def test_chebyshev_bias_first_lead_change(flags):
    assert pc.first_lead_change(flags, 100000) == 26861
    assert pc.first_lead_change(flags, 26860) is None


def test_ratio_trend(flags):
    counts = pc.prime_counts(flags, [10 ** 3, 10 ** 4, 10 ** 5])
    ratios = [c / (x / math.log(x)) for c, x in zip(counts, [1e3, 1e4, 1e5])]
    assert ratios[0] > ratios[1] > ratios[2] > 1
