import elementary_number_theory_reciprocity as qr


def test_legendre_values():
    assert [qr.legendre(a, 7) for a in range(1, 7)] == [1, 1, -1, 1, -1, -1]
    assert qr.legendre(14, 7) == 0
    assert qr.legendre(-1, 13) == 1 and qr.legendre(-1, 11) == -1


def test_reciprocity_small_primes():
    for p in qr.odd_primes_below(60):
        for q in qr.odd_primes_below(60):
            if p != q:
                sign = (-1) ** (((p - 1) // 2) * ((q - 1) // 2))
                assert qr.legendre(p, q) * qr.legendre(q, p) == sign


def test_gauss_lemma():
    for p in qr.odd_primes_below(80):
        for a in range(1, p):
            assert qr.gauss_lemma(a, p) == qr.legendre(a, p)


def test_lattice_points():
    assert qr.lattice_points(7, 11) == (8, 7)
    assert qr.lattice_points(3, 5) == (1, 1)
    assert sum(qr.lattice_points(13, 17)) == 6 * 8


def test_two_squares():
    assert qr.two_squares(13) == (2, 3)
    assert qr.two_squares(2) == (1, 1)
    assert qr.two_squares(7) is None
    assert qr.two_squares(25) == (0, 5)
    for p in qr.odd_primes_below(500):
        assert (qr.two_squares(p) is not None) == (p % 4 == 1)
