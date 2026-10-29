import langlands_programme_reciprocity as rc


def test_primes_below():
    assert rc.primes_below(20) == [2, 3, 5, 7, 11, 13, 17, 19]
    assert len(rc.primes_below(2000)) == 303


def test_legendre_symbol_values():
    # squares mod 7 are 1, 2, 4
    assert [rc.legendre(a, 7) for a in range(1, 7)] == [1, 1, -1, 1, -1, -1]
    assert rc.legendre(0, 11) == 0
    assert rc.legendre(-1, 13) == 1 and rc.legendre(-1, 11) == -1


def test_quadratic_reciprocity_small_primes():
    assert rc.reciprocity_failures(rc.primes_below(120)) == []


def test_reciprocity_check_detects_wrong_law(monkeypatch):
    monkeypatch.setattr(rc, "legendre", lambda a, p: 1)
    assert rc.reciprocity_failures([3, 5, 7, 11]) != []


def test_root_counts():
    assert rc.root_count([1, 0, 1], 5) == 2      # x^2 + 1 mod 5: 2, 3
    assert rc.root_count([1, 0, 1], 7) == 0
    assert rc.root_count([1, 0, -1, -1], 59) == 3
    assert rc.root_count([1, 0, -1, -1], 13) == 0
    assert rc.root_count([1, 0, -1, -1], 23) == 2  # double root: 23 ramifies


def test_eta_product_coefficients():
    a = rc.eta_product_coefficients(30, [1, 23])
    assert a[1:10] == [1, -1, -1, 0, 0, 1, 0, 1, 0]
    # Euler's pentagonal number theorem for prod (1 - q^n): q * (1 - q - q^2 + q^5 + ...)
    e = rc.eta_product_coefficients(20, [1])
    assert [n for n in range(1, 21) if e[n] != 0] == [1, 2, 3, 6, 8, 13, 16]


def test_modular_form_predicts_cubic_roots():
    a = rc.eta_product_coefficients(600, [1, 23])
    for p in rc.primes_below(600):
        if p != 23:
            assert rc.root_count([1, 0, -1, -1], p) == a[p] + 1
