from fractions import Fraction

import rational_numbers_sqrt2_gaps as rs


def test_no_rational_square_root_of_two_found():
    assert rs.square_root_two_search(2000) == []


def test_search_would_find_a_real_hit():
    # Sanity check of the method: the same candidate p = isqrt(2 q^2) is
    # exactly what would be found if a solution existed; for 4 q^2 (= (2q)^2)
    # the analogous search succeeds every time.
    from math import isqrt
    assert all(isqrt(4 * q * q) ** 2 == 4 * q * q for q in range(1, 200))


def test_squeeze_keeps_sqrt2_inside_and_halves_width():
    history = rs.squeeze(12)
    assert len(history) == 13
    for k, (lo, hi) in enumerate(history):
        assert lo * lo < 2 < hi * hi
        assert hi - lo == Fraction(1, 2 ** k)
        assert isinstance(lo, Fraction) and isinstance(hi, Fraction)


def test_pell_fractions_miss_two_by_one_over_q_squared():
    fracs = rs.pell_fractions(10)
    assert fracs[:5] == [(1, 1), (3, 2), (7, 5), (17, 12), (41, 29)]
    for p, q in fracs:
        assert abs(p * p - 2 * q * q) == 1
        assert abs(Fraction(p, q) ** 2 - 2) == Fraction(1, q * q)


def test_pell_signs_alternate():
    signs = [p * p - 2 * q * q for p, q in rs.pell_fractions(8)]
    assert signs == [-1, 1, -1, 1, -1, 1, -1, 1]
