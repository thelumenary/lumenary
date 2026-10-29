import fields_galois_frobenius_cycles as ff


def test_primes():
    assert ff.primes_below(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


def test_factor_degrees_small_cases():
    # x^2 - 2 splits mod 7 (3^2 = 2) and is irreducible mod 5
    assert ff.factor_degrees([-2, 0, 1], 7) == (1, 1)
    assert ff.factor_degrees([-2, 0, 1], 5) == (2,)
    # x^4 + 1 splits completely mod 17 (17 = 1 mod 8) and into quadratics mod 3
    assert ff.factor_degrees([1, 0, 0, 0, 1], 17) == (1, 1, 1, 1)
    assert ff.factor_degrees([1, 0, 0, 0, 1], 3) == (2, 2)


def test_factor_degrees_against_root_count():
    f = [-2, 0, 0, 1]
    for p in ff.primes_below(200):
        if ff.is_squarefree_mod(f, p):
            roots = sum((x ** 3 - 2) % p == 0 for x in range(p))
            assert ff.factor_degrees(f, p).count(1) == roots


def test_x4_plus_1_never_irreducible_mod_p():
    for p in ff.primes_below(500)[1:]:
        assert ff.factor_degrees([1, 0, 0, 0, 1], p) in {(1, 1, 1, 1), (2, 2)}


def test_predictions_are_distributions():
    for _, f, _, predicted in ff.EXAMPLES:
        assert sum(predicted.values()) == 1
        assert all(sum(t) == len(f) - 1 for t in predicted)


def test_frequencies_roughly_match():
    for _, f, _, predicted in ff.EXAMPLES[:3]:
        counts = ff.tally(f, 2000)
        total = sum(counts.values())
        assert set(counts) <= set(predicted)
        for pattern, share in predicted.items():
            assert abs(counts.get(pattern, 0) / total - float(share)) < 0.06


def test_polynomial_helpers():
    assert ff.pmod([1, 0, 1], [1, 1], 2) == []          # x^2 + 1 = (x + 1)^2 mod 2
    assert ff.pgcd([1, 0, 1], [1, 1], 2) == [1, 1]
    assert ff.pdiv([1, 0, 1], [1, 1], 2) == [1, 1]
    assert ff.ppowmod([0, 1], 4, [1, 1, 1], 2) == [0, 1]  # x^4 = x in F_4
