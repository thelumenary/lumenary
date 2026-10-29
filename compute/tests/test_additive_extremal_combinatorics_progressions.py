import itertools

import additive_extremal_combinatorics_progressions as pg


def brute_roth(N):
    best = 0
    for k in range(N + 1):
        if any(not pg.has_three_ap(c) for c in itertools.combinations(range(N), k)):
            best = k
        else:
            break
    return best


def test_has_three_ap():
    assert pg.has_three_ap([1, 2, 3])
    assert pg.has_three_ap([0, 5, 9, 10])  # 0, 5, 10
    assert not pg.has_three_ap([0, 1, 3, 4, 9, 10, 12, 13])
    assert not pg.has_three_ap([])


def test_roth_numbers_match_brute_force():
    values = pg.roth_numbers(14)
    assert values == [brute_roth(N) for N in range(1, 15)]
    assert values[13] == 8  # r3(14) = 8, matching the lesson's Lean bound


def test_roth_number_with_and_without_table():
    table = [0] + pg.roth_numbers(19)
    assert pg.roth_number(20) == pg.roth_number(20, table) == 9


def test_base3_sets_are_ap_free_and_dense_enough():
    for N in (10, 27, 81, 100):
        b = pg.base3_set(N)
        assert not pg.has_three_ap(b)
    assert len(pg.base3_set(81)) == 16  # 2^4 numbers below 3^4


def test_prime_progressions():
    assert pg.smallest_prime_progression(3) == [3, 5, 7]
    assert pg.smallest_prime_progression(6) == [7, 37, 67, 97, 127, 157]
    ap = pg.smallest_prime_progression(7)
    sieve = pg.prime_sieve(1000)
    assert all(sieve[p] for p in ap)
    assert len({b - a for a, b in zip(ap, ap[1:])}) == 1
    assert pg.smallest_prime_progression(7, limit=100) is None


def test_sum_product():
    assert pg.sum_and_product_sizes([1, 2, 3]) == (5, 6)
    s, p = pg.sum_and_product_sizes([2 ** i for i in range(10)])
    assert p == 19 and s == 55
