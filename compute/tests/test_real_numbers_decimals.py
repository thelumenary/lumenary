from fractions import Fraction

import pytest

import real_numbers_decimals as ex


@pytest.mark.parametrize(
    "p, q, expected",
    [
        (3, 8, (0, "375", "0")),
        (1, 7, (0, "", "142857")),
        (5, 12, (0, "41", "6")),
        (22, 7, (3, "", "142857")),
        (1, 3, (0, "", "3")),
        (7, 1, (7, "", "0")),
    ],
)
def test_decimal_expansion_known(p, q, expected):
    assert ex.decimal_expansion(p, q) == expected


def test_period_bounded_by_denominator_minus_one():
    for q in range(2, 120):
        for p in range(1, q):
            _, _, per = ex.decimal_expansion(p, q)
            assert len(per) <= q - 1
    assert len(ex.decimal_expansion(1, 97)[2]) == 96


def test_expansion_reconstructs_the_fraction():
    # 0.ab(cd...) = (pre + per/(10^len(per) - 1)) / 10^len(pre)
    for p, q in [(1, 7), (5, 12), (13, 55), (22, 7), (1, 97)]:
        whole, pre, per = ex.decimal_expansion(p, q)
        a = Fraction(int(pre or "0"), 10 ** len(pre))
        b = Fraction(int(per), (10 ** len(per) - 1) * 10 ** len(pre))
        assert whole + a + b == Fraction(p, q)


def test_sqrt_and_pi_digits():
    assert ex.sqrt_digits(2, 10) == "4142135623"
    assert ex.sqrt_digits(9, 5) == "00000"
    assert ex.pi_digits(30) == "141592653589793238462643383279"
    assert ex.sqrt_digits(2, 40).startswith("41421356237309504880")


def test_fraction_digits_and_agreement():
    assert ex.fraction_digits(22, 7, 6) == "142857"
    assert ex.agreement(ex.pi_digits(20), ex.fraction_digits(22, 7, 20)) == 2
    assert ex.agreement(ex.pi_digits(20), ex.fraction_digits(355, 113, 20)) == 6
    with pytest.raises(ValueError):
        ex.decimal_expansion(1, 0)
