import itertools

import number_system_constructions_well_defined as wd


def test_relations_are_equivalences_on_small_pairs():
    ints = [(a, b) for a in range(5) for b in range(5)]
    for x, y, z in itertools.product(ints, repeat=3):
        assert wd.int_rel(x, x)
        assert wd.int_rel(x, y) == wd.int_rel(y, x)
        if wd.int_rel(x, y) and wd.int_rel(y, z):
            assert wd.int_rel(x, z)
    fracs = [(a, b) for a in range(-3, 4) for b in range(1, 5)]
    for x, y, z in itertools.product(fracs, repeat=3):
        if wd.frac_rel(x, y) and wd.frac_rel(y, z):
            assert wd.frac_rel(x, z)


def test_correct_operations_are_well_defined():
    ints = [(a, b) for a in range(6) for b in range(6)]
    assert wd.counterexample(ints, wd.int_rel, wd.int_add) is None
    assert wd.counterexample(ints, wd.int_rel, wd.int_mul) is None
    fracs = [(a, b) for a in range(-3, 4) for b in range(1, 5)]
    assert wd.counterexample(fracs, wd.frac_rel, wd.frac_add) is None


def test_wrong_operations_have_counterexamples():
    ints = [(a, b) for a in range(4) for b in range(4)]
    p, p2, q, q2 = wd.counterexample(ints, wd.int_rel, wd.int_bad)
    assert wd.int_rel(p, p2) and wd.int_rel(q, q2)
    assert not wd.int_rel(wd.int_bad(p, q), wd.int_bad(p2, q2))
    assert not wd.frac_rel(wd.mediant((1, 2), (1, 3)), wd.mediant((2, 4), (1, 3)))


def test_pairs_model_integer_arithmetic():
    for p, q in itertools.product([(a, b) for a in range(5) for b in range(5)], repeat=2):
        value = lambda r: r[0] - r[1]
        assert value(wd.int_add(p, q)) == value(p) + value(q)
        assert value(wd.int_mul(p, q)) == value(p) * value(q)


def test_zero_divisors_break_transitivity():
    assert wd.transitivity_failure(5) is None
    assert wd.transitivity_failure(7) is None
    x, y, z = wd.transitivity_failure(6)
    assert (x, y, z) == ((0, 1), (0, 2), (3, 1))
    assert wd.transitivity_failure(4) is not None
