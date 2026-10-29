import itertools
import random

import pytest

import information_theory_channel_codes as ex


def test_capacity_values():
    assert ex.capacity(0) == 1.0
    assert ex.capacity(0.5) == pytest.approx(0.0)
    assert ex.capacity(0.1) == pytest.approx(ex.capacity(0.9))
    assert ex.capacity(0.11) == pytest.approx(0.5, abs=0.002)


def test_repetition_error():
    assert ex.repetition_error(1, 0.1) == pytest.approx(0.1)
    assert ex.repetition_error(3, 0.1) == pytest.approx(3 * 0.01 * 0.9 + 0.001)
    with pytest.raises(ValueError):
        ex.repetition_error(4, 0.1)


def test_hamming_codewords_and_distance():
    words = [ex.encode(list(m)) for m in itertools.product((0, 1), repeat=4)]
    assert all(not any(ex.syndrome(w)) for w in words)
    distances = [sum(a != b for a, b in zip(u, v))
                 for u, v in itertools.combinations(words, 2)]
    assert min(distances) == 3  # hence every single error is correctable


def test_decode_corrects_every_single_flip():
    for m in itertools.product((0, 1), repeat=4):
        w = ex.encode(list(m))
        assert ex.decode(w) == list(m)
        for j in range(7):
            flipped = list(w)
            flipped[j] ^= 1
            assert ex.decode(flipped) == list(m)


def test_hamming_block_error_formula():
    assert ex.hamming_block_error(0.0) == pytest.approx(0.0)
    p = 0.05
    assert ex.hamming_block_error(p) == pytest.approx(
        sum(ex.math.comb(7, k) * p ** k * (1 - p) ** (7 - k) for k in range(2, 8)))


def test_simulation_close_to_exact():
    sim = ex.simulate_hamming(0.05, 5000, random.Random(3))
    assert abs(sim - ex.hamming_block_error(0.05)) < 0.01
