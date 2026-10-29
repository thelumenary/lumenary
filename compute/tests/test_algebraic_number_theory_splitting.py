import algebraic_number_theory_splitting as ns


def test_discriminants_and_minimal_polynomials():
    assert ns.discriminant(-1) == -4
    assert ns.discriminant(-5) == -20
    assert ns.discriminant(5) == 5
    assert ns.discriminant(-3) == -3
    assert ns.min_poly(5) == (-1, -1)        # golden ratio: x^2 - x - 1
    assert ns.min_poly(-1) == (0, 1)         # i: x^2 + 1


def test_gaussian_integers():
    assert ns.splitting_type(-1, 2) == "ramified"   # 2 = -i (1 + i)^2
    assert ns.splitting_type(-1, 5) == "split"      # 5 = (2 + i)(2 - i)
    assert ns.splitting_type(-1, 3) == "inert"
    for p in (13, 17, 29, 37, 41):
        assert ns.splitting_type(-1, p) == "split"
    for p in (7, 11, 19, 23, 31):
        assert ns.splitting_type(-1, p) == "inert"


def test_dedekind_kummer_matches_kronecker():
    for d in (-1, -2, -3, -5, -7, 2, 3, 5, 6, 13):
        D = ns.discriminant(d)
        for p in range(2, 300):
            if ns.is_prime(p):
                predicted = ns.PREDICTION[ns.kronecker(D, p)]
                assert ns.splitting_type(d, p) == predicted, (d, p)


def test_ramified_primes_divide_discriminant():
    for d in (-5, 2, 5, -7, 10):
        D = ns.discriminant(d)
        ram = [p for p in range(2, 100)
               if ns.is_prime(p) and ns.splitting_type(d, p) == "ramified"]
        assert ram == [p for p in range(2, 100)
                       if ns.is_prime(p) and D % p == 0]


def test_principal_split_primes_of_sqrt_minus_five():
    assert ns.norm_form_represents(29, -5)          # 29 = 3^2 + 5 * 2^2
    assert not ns.norm_form_represents(3, -5)       # 3 = P P', P = (3, 1 + sqrt-5)
    for p in range(3, 400):
        if ns.is_prime(p) and ns.splitting_type(-5, p) == "split":
            assert ns.norm_form_represents(p, -5) == (p % 20 in (1, 9))
