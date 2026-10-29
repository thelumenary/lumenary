import logic_statements_counterexamples as lc


def test_primes():
    assert [n for n in range(30) if lc.is_prime(n)] == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert not lc.is_prime(1) and not lc.is_prime(9) and lc.is_prime(10007)


def test_sum_of_two_primes():
    assert lc.sum_of_two_primes(4) and lc.sum_of_two_primes(28)
    # An odd sum of two primes must use the prime 2, and 11 - 2 = 9 is not prime.
    assert not lc.sum_of_two_primes(11)
    assert all(lc.sum_of_two_primes(n) for n in range(4, 500, 2))


def test_ending_in_two():
    text, about, holds = lc.CLAIMS[0]
    fits, bad, first = lc.hunt(about, holds, 100)
    assert (fits, bad, first) == (5, 5, 2)
    assert about(22) and not holds(22)


def test_odd_primes_claim_fails_at_nine():
    _, about, holds = lc.CLAIMS[1]
    assert lc.hunt(about, holds, 20)[2] == 9


def test_ten_successes_then_failure():
    _, about, holds = lc.CLAIMS[2]
    assert all(holds(n) for n in range(10))
    assert not holds(10) and 10 * 10 + 10 + 11 == 11 * 11
    assert lc.hunt(about, holds)[2] == 10


def test_no_counterexample_for_goldbach_and_doubles():
    for _, about, holds in lc.CLAIMS[3:]:
        assert lc.hunt(about, holds, 2000)[1:] == (0, None)
