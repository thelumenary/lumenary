import commutative_algebra_spec_zmod as sz


def test_ideals_of_z12():
    ids = sz.ideals(12)
    assert sorted(ids) == [1, 2, 3, 4, 6, 12]
    assert ids[4] == frozenset({0, 4, 8})
    assert ids[12] == frozenset({0})


def test_prime_and_maximal_ideals():
    assert sz.is_prime_ideal(12, sz.ideal(12, 2))
    assert not sz.is_prime_ideal(12, sz.ideal(12, 4))      # 2 * 2 in (4)
    assert not sz.is_prime_ideal(12, sz.ideal(12, 1))      # not proper
    assert sz.is_maximal_ideal(12, sz.ideal(12, 3))
    assert not sz.is_maximal_ideal(12, sz.ideal(12, 6))
    for n in range(2, 40):
        for i in sz.ideals(n).values():
            assert sz.is_prime_ideal(n, i) == sz.is_maximal_ideal(n, i)


def test_radicals():
    assert sz.nilradical(12) == frozenset({0, 6})
    assert sz.nilradical(7) == frozenset({0})
    assert sz.jacobson(8) == frozenset({0, 2, 4, 6})
    for n in range(2, 40):
        assert sz.nilradical(n) == sz.jacobson(n)


def test_localisation_is_p_part():
    assert sz.localisation_size(12, 2) == 4
    assert sz.localisation_size(12, 3) == 3
    assert sz.localisation_size(8, 2) == 8         # already local
    for n in range(2, 50):
        for p in sz.prime_divisors(n):
            assert sz.localisation_size(n, p) == sz.p_part(n, p)


def test_nakayama_in_local_rings():
    for n in (2, 4, 8, 9, 25, 27, 32):
        assert sz.nakayama_holds(n)
    assert sz.prime_divisors(60) == {2, 3, 5}
