from fractions import Fraction
import math

import experimental_mathematics_integer_relations as ir


def test_pi_and_e_to_many_digits():
    p = ir.pi_fraction(50)
    # first 50 decimals of pi
    ref = Fraction(31415926535897932384626433832795028841971693993751, 10 ** 49)
    assert abs(p - ref) < Fraction(1, 10 ** 48)
    assert abs(float(ir.e_fraction(30)) - math.e) < 1e-15


def test_bbp_relation_holds_to_high_precision():
    xs = [ir.pi_fraction(80)] + [ir.bbp_sum(j, 80) for j in range(1, 9)]
    rel = [1, -4, 0, 0, 2, 1, 1, 0, 0]
    assert ir.residual(rel, xs) < Fraction(1, 10 ** 75)


def test_pslq_finds_the_bbp_relation_and_a_known_relation():
    xs = [ir.pi_fraction(60)] + [ir.bbp_sum(j, 60) for j in range(1, 9)]
    rel, _, _ = ir.pslq(xs, 60, max_norm=10 ** 12)
    assert rel == [1, -4, 0, 0, 2, 1, 1, 0, 0]
    # rational inputs always have integer relations, and PSLQ must find one
    rel2, _, _ = ir.pslq([Fraction(1), Fraction(2, 3), Fraction(1, 7)], 30,
                         max_norm=10 ** 6)
    assert rel2 is not None
    assert ir.residual(rel2, [Fraction(1), Fraction(2, 3), Fraction(1, 7)]) == 0


def test_pslq_bound_when_no_small_relation():
    xs = [ir.pi_fraction(40), ir.e_fraction(40), Fraction(1)]
    rel, _, bound = ir.pslq(xs, 40, max_norm=10 ** 10)
    assert rel is None and bound > 10 ** 10


def test_low_precision_relation_is_spurious():
    low = [ir.pi_fraction(8), ir.e_fraction(8), Fraction(1)]
    fake, _, _ = ir.pslq(low, 8, max_norm=10 ** 6)
    high = [ir.pi_fraction(40), ir.e_fraction(40), Fraction(1)]
    assert fake is not None
    assert ir.residual(fake, high) > Fraction(1, 10 ** 8)


def test_hex_digits():
    assert ir.exact_hex_digits(0, 16) == "243F6A8885A308D3"
    assert ir.bbp_hex_digits(0, 8) == "243F6A88"
    assert ir.bbp_hex_digits(1000, 8) == ir.exact_hex_digits(1000, 8)
    assert ir.bbp_hex_digits(5000, 8) == ir.exact_hex_digits(5000, 8)


def test_format_combination():
    assert ir.format_combination([1, -4, 0, 0, 2, 1, 1, 0, 0]) == \
        "4 S_1 - 2 S_4 - S_5 - S_6"
