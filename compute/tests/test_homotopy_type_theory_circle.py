from itertools import product

import pytest

import homotopy_type_theory_circle as hc


def test_encode_and_decode_basic_values():
    assert hc.encode(()) == 0
    assert hc.encode((1, 1, -1, 1)) == 2
    assert hc.decode(3) == (1, 1, 1)
    assert hc.decode(-2) == (-1, -1)
    assert hc.decode(0) == ()
    with pytest.raises(ValueError):
        hc.encode((1, 2))


@pytest.mark.parametrize("n", range(-20, 21))
def test_encode_decode_round_trip(n):
    assert hc.encode(hc.decode(n)) == n
    assert hc.reduce_word(hc.decode(n)) == hc.decode(n)


def test_reduction_is_determined_by_winding_number():
    for w in hc.all_words(10):
        assert hc.decode(hc.encode(w)) == hc.reduce_word(w)
        # Reduction never changes the winding number.
        assert hc.encode(hc.reduce_word(w)) == hc.encode(w)


def test_encode_is_a_homomorphism_and_respects_inverses():
    words = list(hc.all_words(5))
    for u in words:
        assert hc.encode(u + hc.inverse(u)) == 0
        assert hc.reduce_word(u + hc.inverse(u)) == ()
        for v in words[:40]:
            assert hc.encode(u + v) == hc.encode(u) + hc.encode(v)


def test_number_of_words():
    assert len(list(hc.all_words(12))) == 2 ** 13 - 2
    null = [w for w in product((1, -1), repeat=8) if hc.encode(w) == 0]
    assert len(null) == 70


@pytest.mark.parametrize("turns", [-3, -1, 0, 1, 2, 5])
def test_numerical_winding_numbers(turns):
    w = hc.winding_number(hc.wobbly_loop(turns))
    assert abs(w - turns) < 1e-9


def test_winding_number_of_off_centre_circle_is_zero():
    import cmath
    import math
    # A circle of radius 1 centred at 3 does not wind round the origin.
    curve = lambda t: 3 + cmath.exp(2j * math.pi * t)
    assert abs(hc.winding_number(curve)) < 1e-9
