import rings_factorisation_norms as rf


def test_norm_is_multiplicative():
    for d in (-1, -5):
        for z in [(1, 1), (2, -3), (0, 4), (5, 0)]:
            for w in [(1, -1), (3, 2), (-2, 1)]:
                assert rf.norm(rf.mul(z, w, d), d) == rf.norm(z, d) * rf.norm(w, d)


def test_units():
    assert sorted(rf.units(-1)) == [(-1, 0), (0, -1), (0, 1), (1, 0)]
    assert sorted(rf.units(-5)) == [(-1, 0), (1, 0)]


def test_divide():
    assert rf.divide((6, 0), (1, 1), -5) == (1, -1)
    assert rf.divide((1, 1), (2, 0), -5) is None
    assert rf.divide((5, 0), (2, 1), -1) == (2, -1)


def test_no_elements_of_norm_two_or_three_in_z_sqrt_minus5():
    assert rf.of_norm(2, -5) == [] and rf.of_norm(3, -5) == []
    for z in [(2, 0), (3, 0), (1, 1), (1, -1)]:
        assert rf.is_irreducible(z, -5)


def test_unique_factorisation_in_gaussian_integers():
    for n in range(2, 31):
        assert len(rf.factorisations((n, 0), -1)) == 1
    (fac,) = rf.factorisations((5, 0), -1)
    assert len(fac) == 2  # 5 = (2 + i)(2 - i)
    assert rf.is_irreducible((3, 0), -1) and not rf.is_irreducible((5, 0), -1)


def test_non_unique_factorisation_of_six():
    facs = rf.factorisations((6, 0), -5)
    assert len(facs) == 2
    assert {len(f) for f in facs} == {2}


def test_euclid_fails_for_z_sqrt_minus5_and_works_for_z_i():
    assert rf.best_remainder((1, 1), (2, 0), -5) == 6
    assert rf.gaussian_rounding_works(4)


def test_show():
    assert rf.show((1, -1), -5) == "1-r"
    assert rf.show((0, 2), -1) == "2i"
    assert rf.show((7, 0), -5) == "7"
