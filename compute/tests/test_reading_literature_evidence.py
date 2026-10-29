import reading_literature_evidence as ev


def brute_goldbach(n, primes):
    return sum(1 for p in primes if p <= n - p and (n - p) in primes)


def test_mobius_and_mertens_known_values():
    mu = ev.mobius_sieve(30)
    assert list(mu[1:11]) == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1]
    assert mu[30] == -1 and mu[12] == 0
    m = ev.mertens(10 ** 6)
    assert [int(m[10 ** k]) for k in range(1, 7)] == [-1, 1, 2, -23, -48, 212]


def test_mertens_ratio():
    m = ev.mertens(10 ** 5)
    n, worst = ev.worst_mertens_ratio(m, 2, 10 ** 5)
    assert n == 5 and abs(worst - 2 / 5 ** 0.5) < 1e-12
    n2, worst2 = ev.worst_mertens_ratio(m, 10 ** 4, 10 ** 5)
    assert worst2 < 0.6 and 10 ** 4 <= n2 <= 10 ** 5


def test_goldbach_counts_match_brute_force():
    limit = 2000
    r = ev.goldbach_counts(limit)
    primes = {p for p in range(2, limit + 1)
              if all(p % d for d in range(2, int(p ** 0.5) + 1))}
    for n in range(4, limit + 1, 2):
        assert r[n] == brute_goldbach(n, primes), n
    assert r[4] == 1 and r[10] == 2 and r[100] == 6


def test_goldbach_holds_in_range_and_minima_grow():
    limit = 2 * 10 ** 5
    r = ev.goldbach_counts(limit)
    assert (r[4::2] >= 1).all()
    minima = [least for _, _, least in ev.decade_minima(r, limit)]
    assert minima == sorted(minima)
    assert minima[-1] > 100
