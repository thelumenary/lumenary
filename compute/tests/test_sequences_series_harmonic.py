import math
from fractions import Fraction

import pytest

import sequences_series_harmonic as ex


def test_oresme_blocks_at_least_half():
    assert ex.oresme_block(0) == Fraction(1, 2)
    assert ex.oresme_block(1) == Fraction(1, 3) + Fraction(1, 4)
    for k in range(9):
        assert ex.oresme_block(k) >= Fraction(1, 2)
    with pytest.raises(ValueError):
        ex.oresme_block(-1)


def test_blocks_add_up_to_harmonic_numbers():
    # H(2^m) = 1 + (block 0) + ... + (block m-1) >= 1 + m/2
    for m in range(7):
        h = ex.harmonic_exact(2 ** m)
        assert h == 1 + sum((ex.oresme_block(k) for k in range(m)), Fraction(0))
        assert h >= 1 + Fraction(m, 2)


def test_first_exceeding_known_values():
    # OEIS A002387 (least n with H_n > t), t = 1..10
    expected = [2, 4, 11, 31, 83, 227, 616, 1674, 4550, 12367]
    assert ex.first_exceeding(list(range(1, 11))) == expected


def test_first_exceeding_is_exact_at_small_thresholds():
    for t, n in zip(range(1, 4), ex.first_exceeding([1, 2, 3])):
        assert ex.harmonic_exact(n) > t >= ex.harmonic_exact(n - 1)


def test_basel_partial_sums_bounded():
    assert ex.basel_partial(1) == 1.0
    assert ex.basel_partial(100000) < math.pi ** 2 / 6 < 2
    assert math.isclose(ex.basel_partial(100000), math.pi ** 2 / 6, abs_tol=1e-4)
