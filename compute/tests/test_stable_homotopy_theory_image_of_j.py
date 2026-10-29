from fractions import Fraction

import stable_homotopy_theory_image_of_j as j


def test_bernoulli_numbers():
    b = j.bernoulli_numbers(12)
    assert b[0] == 1 and b[1] == Fraction(-1, 2)
    assert b[2] == Fraction(1, 6) and b[4] == Fraction(-1, 30)
    assert b[6] == Fraction(1, 42) and b[12] == Fraction(-691, 2730)
    assert all(b[k] == 0 for k in range(3, 13, 2))


def test_image_of_j_orders_match_known_stems():
    b = j.bernoulli_numbers(16)
    assert [j.image_of_j_order(k, b) for k in range(1, 5)] == [24, 240, 504, 480]
    for k, (order, _) in j.KNOWN_STEMS.items():
        assert order % j.image_of_j_order(k, b) == 0


def test_kervaire_milnor_counts():
    b = j.bernoulli_numbers(16)
    assert j.bp_order(2, b) == 28
    assert j.bp_order(3, b) == 992
    assert j.bp_order(4, b) == 8128


def test_m_is_divisible_by_24_pattern():
    # m(2k) is always divisible by 24 (von Staudt-Clausen: 2 and 3 divide the
    # denominator of B_2k / 4k).
    b = j.bernoulli_numbers(24)
    assert all(j.image_of_j_order(k, b) % 24 == 0 for k in range(1, 13))
