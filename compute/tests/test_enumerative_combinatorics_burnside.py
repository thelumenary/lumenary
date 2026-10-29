from fractions import Fraction

import enumerative_combinatorics_burnside as eb


def test_cube_group_has_24_rotations_with_right_cycle_types():
    cube = eb.cube_rotations()
    assert len(cube) == 24
    counts = sorted(eb.cycles(g) for g in cube)
    assert [counts.count(c) for c in range(1, 7)] == [0, 8, 12, 3, 0, 1]


def test_cube_colourings_match_polya():
    cube = eb.cube_rotations()
    for k in (1, 2, 3):
        polya = Fraction(k**6 + 3 * k**4 + 12 * k**3 + 8 * k**2, 24)
        assert eb.orbits_burnside(cube, k) == polya
        assert eb.orbits_brute_force(cube, k, 6) == polya


def test_necklaces_three_ways():
    for n in range(1, 9):
        for k in (2, 3):
            group = eb.rotations(n)
            brute = eb.orbits_brute_force(group, k, n)
            assert brute == eb.orbits_burnside(group, k) == eb.necklace_formula(n, k)


def test_naive_count_is_wrong_but_close_for_primes():
    # for prime n, Burnside gives (k^n - k)/n + k, not k^n / n
    for n in (5, 7):
        assert eb.necklace_formula(n, 2) == Fraction(2**n - 2, n) + 2
        assert eb.necklace_formula(n, 2) != Fraction(2**n, n)


def test_bracelets_and_totient():
    assert [eb.phi(n) for n in range(1, 11)] == [1, 1, 2, 2, 4, 2, 6, 4, 6, 4]
    assert eb.orbits_brute_force(eb.dihedral(6), 2, 6) == 13
    assert eb.orbits_burnside(eb.dihedral(7), 3) == 198
