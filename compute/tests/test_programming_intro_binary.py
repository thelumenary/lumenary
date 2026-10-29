from fractions import Fraction

import programming_intro_binary as pb


def test_division_steps():
    assert pb.division_steps(0) == []
    assert pb.division_steps(6) == [(6, 3, 0), (3, 1, 1), (1, 0, 1)]
    for n, q, r in pb.division_steps(45):
        assert n == 2 * q + r and r in (0, 1)


def test_to_and_from_binary():
    assert pb.to_binary(0) == "0"
    assert pb.to_binary(13) == "1101"
    assert pb.to_binary(45) == "101101"
    assert pb.from_binary("101101") == 45
    assert pb.from_binary("0") == 0
    for n in range(2000):
        assert pb.to_binary(n) == bin(n)[2:]
        assert pb.from_binary(pb.to_binary(n)) == n


def test_strings_without_leading_zeros_are_a_perfect_naming():
    names = pb.strings_without_leading_zeros(10)
    assert len(names) == len(set(names)) == 1024
    assert all(s == "0" or s[0] == "1" for s in names)
    assert sorted(pb.from_binary(s) for s in names) == list(range(1024))
    assert pb.strings_without_leading_zeros(2) == ["0", "1", "10", "11"]


def test_binary_fraction_digits():
    assert pb.binary_fraction_digits(Fraction(1, 2), 3) == "100"
    assert pb.binary_fraction_digits(Fraction(3, 8), 4) == "0110"
    assert pb.binary_fraction_digits(Fraction(1, 10), 12) == "000110011001"


def test_floating_point_facts():
    assert 0.1 + 0.2 != 0.3
    assert Fraction(0.1) == Fraction(3602879701896397, 36028797018963968)
    assert Fraction(0.1) != Fraction(1, 10)
    assert Fraction(1, 10) + Fraction(2, 10) == Fraction(3, 10)
    assert sum([0.1] * 10) != 1.0
