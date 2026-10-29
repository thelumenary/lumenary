import commutative_algebra_nullstellensatz as ns

x, y = ns.x, ns.y


def test_ideal_membership():
    assert ns.in_ideal(x**2, [y - x**2, y])
    assert not ns.in_ideal(x, [y - x**2, y])
    assert ns.in_ideal(x**2 - 1, [y - x**2, y - 1])
    assert not ns.in_ideal(1, [x**2 + 1, y])


def test_radical_exponents():
    assert ns.radical_exponent(x, [y - x**2, y]) == 2
    assert ns.radical_exponent(x, [y**2 - x**3, y]) == 3
    assert ns.radical_exponent(y, [x**2 + y**2 - 1, x - 1]) == 2
    assert ns.radical_exponent(y, [x**2, x * y]) is None
    assert ns.radical_exponent(x, [x**3], max_k=2) is None


def test_rabinowitsch_agrees_with_powers():
    for _, gens, f in ns.EXAMPLES:
        k = ns.radical_exponent(f, gens)
        assert (k is not None) == ns.in_radical(f, gens)


def test_weak_nullstellensatz_examples():
    assert ns.is_proper([x**2 + 1, y])          # complex zeros only
    assert not ns.is_proper([x * y - 1, x])      # no zeros at all
    assert not ns.is_proper([x, x - 1])          # parallel lines x = 0, x = 1
    assert ns.is_proper([x, y])                  # the origin
