import itertools
import math

import monoidal_categories_pentagon as mp


def catalan(k):
    return math.comb(2 * k, k) // (k + 1)


def test_bracketings_are_counted_by_catalan_numbers():
    for n in range(1, 8):
        assert len(mp.bracketings(tuple(range(n)))) == catalan(n - 1)
    assert mp.bracketings((0, 1, 2)) == [(0, (1, 2)), ((0, 1), 2)]


def test_associahedron_small_cases():
    assert mp.associahedron(3) == (2, 1)
    assert mp.associahedron(4) == (5, 5)    # the pentagon
    assert mp.associahedron(5) == (14, 21)  # the 3-dimensional associahedron
    assert mp.associahedron(6) == (42, 84)


def test_moves_apply_the_associator_anywhere():
    assert mp.moves(((0, 1), 2)) == [((0, (1, 2)), (0, 1, 2))]
    assert mp.moves((0, (1, 2))) == []
    results = [t for t, _ in mp.moves((((0, 1), 2), 3))]
    assert ((0, 1), (2, 3)) in results and ((0, (1, 2)), 3) in results


def test_carry_cochain_is_a_normalised_cocycle():
    for n in range(2, 8):
        for p in range(n):
            w = mp.carry_cochain(p, n)
            assert mp.cocycle_failures(w, n) == []
            assert all(w(a, 0, c) == 0 for a in range(n) for c in range(n))


def test_naive_and_random_cochains_fail():
    assert mp.cocycle_failures(mp.naive_cochain(3), 3)[0] == (1, 2, 0, 0)
    # w(a, b, c) = b is not a cocycle either
    assert mp.cocycle_failures(lambda a, b, c: b, 3)


def test_trilinear_cochain_is_a_cocycle():
    # Any trilinear form is a cocycle - a sanity check of the checker.
    assert mp.cocycle_failures(lambda a, b, c: a * b * c % 5, 5) == []


def test_path_independence_matches_cocycle_condition():
    w = mp.carry_cochain(2, 3)
    assert all(mp.path_independent(w, g, 3)
               for g in itertools.product(range(3), repeat=4))
    assert not mp.path_independent(mp.naive_cochain(3), (1, 2, 0, 0), 3)
    # With all grades zero every twist vanishes.
    assert mp.path_independent(mp.naive_cochain(3), (0, 0, 0, 0, 0), 3)
