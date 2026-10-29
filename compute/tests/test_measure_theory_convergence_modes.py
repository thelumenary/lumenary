from fractions import Fraction

import pytest

import measure_theory_convergence_modes as cm


def test_escaping_mass_integral_is_one_but_pointwise_zero():
    assert all(cm.escaping_integral(n) == 1 for n in range(1, 200))
    for x in [Fraction(1, 7), Fraction(1, 1000), Fraction(-1), Fraction(0), Fraction(3)]:
        # eventually zero: for n >= 1/x (or always, when x <= 0)
        assert all(cm.escaping(n, x) == 0 for n in range(1001, 1100))
    assert cm.escaping(5, Fraction(1, 10)) == 5
    assert cm.escaping(10, Fraction(1, 10)) == 0  # open interval


def test_travelling_bump():
    assert [cm.bump(n, 2) for n in range(4)] == [0, 1, 1, 0]
    assert all(cm.bump(n, Fraction(5, 2)) == 0 for n in range(3, 50))


def test_power_integrals_tend_to_zero():
    assert cm.power_integral(0) == 1
    assert cm.power_integral(9) == Fraction(1, 10)
    vals = [cm.power_integral(n) for n in range(50)]
    assert all(a > b for a, b in zip(vals, vals[1:]))


def test_typewriter_intervals_cover_each_block():
    with pytest.raises(ValueError):
        cm.typewriter_interval(0)
    for m in range(6):
        block = [cm.typewriter_interval(k) for k in range(2 ** m, 2 ** (m + 1))]
        assert block[0][0] == 0 and block[-1][1] == 1
        assert all(b == c for (_, b), (c, _) in zip(block, block[1:]))
        assert all(cm.typewriter_integral(k) == Fraction(1, 2 ** m)
                   for k in range(2 ** m, 2 ** (m + 1)))


def test_typewriter_hits_one_third_once_per_block():
    h = cm.hits(2 ** 12 - 1, Fraction(1, 3))
    assert len(h) == 12
    assert [k.bit_length() - 1 for k in h] == list(range(12))
    # and misses it most of the time
    assert cm.typewriter(2 ** 7, Fraction(1, 3)) == 0
