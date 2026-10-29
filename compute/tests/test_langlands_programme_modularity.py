import langlands_programme_modularity as md


def brute_trace(p):
    affine = sum(1 for x in range(p) for y in range(p)
                 if (y * y + y - (x ** 3 - x * x - 10 * x - 20)) % p == 0)
    return p - affine


def test_series_mul():
    assert md.series_mul([1, 1], [1, 1], 3) == [1, 2, 1]
    assert md.series_mul([1, -1], [1, 1, 1, 1], 4) == [1, 0, 0, 0]


def test_euler_product_pentagonal():
    c = md.euler_product(30)
    nonzero = {k: v for k, v in enumerate(c) if v}
    assert nonzero == {0: 1, 1: -1, 2: -1, 5: 1, 7: 1, 12: -1, 15: -1, 22: 1, 26: 1}


def test_form_11a_coefficients():
    a = md.form_11a()
    assert a[1:11] == [1, -2, -1, 2, 1, 2, -2, 0, -2, -2]


def test_curve_trace_fast_matches_brute_force():
    for p in md.primes_below(80):
        assert md.curve_trace(p) == brute_trace(p)


def test_modularity_of_11a1_small_primes():
    a = md.form_11a()
    for p in md.primes_below(200):
        assert md.curve_trace(p) == a[p]


def test_tau_values_and_congruence():
    tau = md.ramanujan_tau()
    assert tau[1:11] == [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920]
    for n in range(1, 60):
        assert (tau[n] - md.sigma(n, 11)) % 691 == 0


def test_multiplicativity_checker():
    tau = md.ramanujan_tau()
    assert md.multiplicativity_failures(tau, 100) == []
    fake = list(range(101))  # a_n = n is multiplicative too
    assert md.multiplicativity_failures(fake, 100) == []
    fake[6] = 7
    assert (2, 3) in md.multiplicativity_failures(fake, 100)


def test_sigma():
    assert md.sigma(6, 1) == 12
    assert md.sigma(1, 11) == 1
    assert md.sigma(4, 2) == 21
