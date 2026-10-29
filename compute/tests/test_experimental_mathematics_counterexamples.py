import math
from fractions import Fraction

import experimental_mathematics_counterexamples as ce


def test_euler_search_finds_lander_parkin_only():
    sols = ce.euler_fifth_power_search(150)
    assert sols == [(27, 84, 110, 133, 144)]
    assert 27 ** 5 + 84 ** 5 + 110 ** 5 + 133 ** 5 == 144 ** 5
    # below e = 144 there is nothing
    assert ce.euler_fifth_power_search(143) == []


def test_sieve_and_prime_counts():
    is_prime = ce.prime_sieve(100)
    assert [p for p in range(101) if is_prime[p]][:10] == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert int(is_prime.sum()) == 25
    assert int(ce.prime_sieve(10 ** 4).sum()) == 1229


def test_prime_race_first_reversal_is_26861():
    first, count = ce.race_mod_4(10 ** 5)
    assert first == 26861                      # Leech (1957)
    assert count == 2                          # x = 26861 and 26862 only
    assert 26861 % 4 == 1


def test_li_values():
    assert abs(ce.li(2) - 1.045163780117) < 1e-9
    assert abs(ce.li(1000) - 177.6097) < 1e-3
    assert abs(float(ce.li_array([1000.0])[0]) - ce.li(1000)) < 1e-9


def test_li_exceeds_pi_on_the_range():
    holds, margin = ce.li_exceeds_pi_up_to(10 ** 5)
    assert holds and 0 < margin < 0.05


def test_borwein_pattern_exact():
    rows = ce.borwein_pattern(10)
    assert len(rows) == 7
    assert all(value == Fraction(1, 2) for _, value in rows[:6])
    s, value = rows[6]
    assert s > 1 > rows[5][0]
    assert value == Fraction(467807924713440738696537864469,
                             935615849440640907310521750000)
    assert abs(float(Fraction(1, 2) - value) * math.pi - 2.31e-11) < 1e-13
