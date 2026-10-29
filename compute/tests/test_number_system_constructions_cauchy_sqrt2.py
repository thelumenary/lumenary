from fractions import Fraction

import number_system_constructions_cauchy_sqrt2 as cs


def test_cut_membership():
    assert cs.in_cut(Fraction(-5)) and cs.in_cut(Fraction(0)) and cs.in_cut(Fraction(7, 5))
    assert not cs.in_cut(Fraction(3, 2)) and not cs.in_cut(Fraction(2))


def test_climb_stays_in_cut_and_increases():
    for q in [Fraction(0), Fraction(1), Fraction(7, 5), Fraction(140, 99), Fraction(13, 10)]:
        assert cs.in_cut(q)
        r = cs.climb(q)
        assert q < r and cs.in_cut(r)


def test_babylonian_stays_above():
    for x in cs.iterate(cs.babylonian, 2, 6):
        assert x > 0 and x * x > 2
        assert not cs.in_cut(x)


def test_known_terms_and_shrinking_gap():
    assert cs.iterate(cs.climb, 1, 5) == [Fraction(1), Fraction(4, 3), Fraction(7, 5),
                                          Fraction(24, 17), Fraction(41, 29), Fraction(140, 99)]
    assert cs.iterate(cs.babylonian, 2, 3) == [Fraction(2), Fraction(3, 2), Fraction(17, 12),
                                               Fraction(577, 408)]
    upper, lower = cs.iterate(cs.babylonian, 2, 6), cs.iterate(cs.climb, 1, 6)
    gaps = [u - l for u, l in zip(upper, lower)]
    assert all(g > 0 for g in gaps)
    assert all(b < a for a, b in zip(gaps, gaps[1:]))


def test_no_small_rational_root():
    assert cs.no_rational_root(1000)
    assert not any((Fraction(p, q)) ** 2 == 2 for q in range(1, 60) for p in range(1, 2 * q))
