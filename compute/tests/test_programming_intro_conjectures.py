import programming_intro_conjectures as pc


def test_sum_loops():
    assert pc.sum_loop(0) == 0
    assert pc.sum_loop(10) == 55
    assert pc.sum_loop(100) == 5050
    assert pc.sum_loop_buggy(100) == 4950
    assert all(pc.sum_loop_buggy(n) == pc.sum_loop(n) - n for n in range(1, 50))


def test_sum_of_odds_is_square():
    assert [pc.sum_of_odds(n) for n in range(6)] == [0, 1, 4, 9, 16, 25]


def test_prime_sieve():
    is_prime = pc.prime_sieve(30)
    assert [p for p in range(31) if is_prime[p]] == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    big = pc.prime_sieve(6000)
    assert not big[5777] and not big[5993] and big[5779]


def test_prime_plus_twice_square():
    is_prime = pc.prime_sieve(100)
    p, k = pc.prime_plus_twice_square(27, is_prime)
    assert p + 2 * k * k == 27 and is_prime[p]
    assert pc.prime_plus_twice_square(9, is_prime) == (7, 1)


def test_goldbach_counterexamples():
    assert pc.goldbach_other_counterexamples(5000) == []
    assert pc.goldbach_other_counterexamples(10000) == [5777, 5993]
    is_prime = pc.prime_sieve(6000)
    assert pc.prime_plus_twice_square(5777, is_prime) is None
    assert 5777 == 53 * 109 and 5993 == 13 * 461
