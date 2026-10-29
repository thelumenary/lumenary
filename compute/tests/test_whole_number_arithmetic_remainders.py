import pytest

import whole_number_arithmetic_remainders as wr


def test_repeated_subtraction_matches_divmod():
    assert wr.repeated_subtraction(347, 30) == (11, 17)
    assert wr.repeated_subtraction(4, 7) == (0, 4)
    assert wr.repeated_subtraction(30, 6) == (5, 0)
    for a in range(200):
        for b in range(1, 15):
            assert wr.repeated_subtraction(a, b) == divmod(a, b)


def test_repeated_subtraction_rejects_bad_input():
    with pytest.raises(ValueError):
        wr.repeated_subtraction(5, 0)
    with pytest.raises(ValueError):
        wr.repeated_subtraction(-1, 3)


def test_all_pairs_with_and_without_the_small_remainder_rule():
    assert wr.all_pairs(347, 30) == [(11, 17)]
    loose = wr.all_pairs(347, 30, small_remainder=False)
    assert len(loose) == 12
    assert loose[0] == (0, 347) and loose[-1] == (11, 17)
    assert all(q * 30 + r == 347 for q, r in loose)
    # 23 = 3 x 5 + 8 is true, but 8 is too big to be the remainder.
    assert (3, 8) in wr.all_pairs(23, 5, small_remainder=False)
    assert wr.all_pairs(23, 5) == [(4, 3)]
    with pytest.raises(ValueError):
        wr.all_pairs(5, 0)


def test_exhaustive_check_finds_unique_pairs():
    cases, unique, agree = wr.exhaustive_check(100, 9)
    assert cases == 101 * 9
    assert unique and agree


def test_division_by_zero_has_no_or_every_answer():
    assert wr.solutions_of_times_zero(5, 1000) == []
    assert wr.solutions_of_times_zero(0, 10) == list(range(11))
