import polynomials_roots_mod_n as prm


def test_roots_of_x_squared_minus_one():
    assert prm.roots_mod([1, 0, -1], 8) == [1, 3, 5, 7]
    assert prm.roots_mod([1, 0, -1], 7) == [1, 6]
    assert prm.roots_mod([1, 0, -1], 2) == [1]
    assert len(prm.roots_mod([1, 0, -1], 24)) == 8


def test_primes_never_exceed_two_roots_for_x2_minus_1():
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        assert len(prm.roots_mod([1, 0, -1], p)) == 2


def test_degree_mod():
    assert prm.degree_mod((0, 0, 3, 1), 5) == 1
    assert prm.degree_mod((5, 0, 1), 5) == 0
    assert prm.degree_mod((0, 0, 0), 3) is None


def test_exhaustive_bound_for_primes():
    for p in (2, 3, 5):
        checked, bad = prm.bound_violations(p, 3)
        assert checked == p ** 4 - 1
        assert bad == 0


def test_bound_fails_modulo_eight():
    checked, bad = prm.bound_violations(8, 2)
    assert checked == 8 ** 3 - 1
    assert bad > 0


def test_zero_divisors():
    assert prm.zero_divisors(8) == [(2, 4), (4, 4), (4, 6)]
    assert prm.zero_divisors(7) == []
