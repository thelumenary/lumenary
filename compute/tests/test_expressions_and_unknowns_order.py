from fractions import Fraction

import expressions_and_unknowns_order as eo


def test_tokens():
    assert eo.tokens("2 + 3 x 4") == [Fraction(2), "+", Fraction(3), "x", Fraction(4)]


def test_the_two_readings_of_two_plus_three_times_four():
    toks = eo.tokens("2 + 3 x 4")
    assert eo.left_to_right(toks) == 20
    assert eo.by_convention(toks) == 14


def test_convention_details():
    assert eo.by_convention(eo.tokens("20 - 8 / 4")) == 18
    assert eo.by_convention(eo.tokens("18 / 3 x 2")) == 12  # same level: left to right
    assert eo.by_convention(eo.tokens("10 - 4 - 3")) == 3
    assert eo.by_convention(eo.tokens("( 2 + 3 ) x 4")) == 20
    assert eo.by_convention(eo.tokens("2 x ( 3 + 4 ) - 1")) == 13
    assert eo.by_convention(eo.tokens("7 / 2")) == Fraction(7, 2)


def test_agreement_table():
    # Same level, or + / - second: the readings always agree.
    for op1 in "+-x/":
        for op2 in "+-":
            assert eo.agreement(op1, op2) == 729
    for op1 in "x/":
        for op2 in "x/":
            assert eo.agreement(op1, op2) == 729
    # + or - before x or /: they agree only when c = 1 (9 x 9 = 81 cases).
    for op1 in "+-":
        for op2 in "x/":
            assert eo.agreement(op1, op2) == 81
