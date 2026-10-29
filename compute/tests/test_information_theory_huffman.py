import math
from fractions import Fraction

import pytest

import information_theory_huffman as ex


def test_frequencies_sum_to_one():
    probs = ex.frequencies(ex.TEXT)
    assert sum(probs.values()) == 1
    assert probs[" "] == Fraction(ex.TEXT.count(" "), len(ex.TEXT))


def test_entropy_simple_cases():
    assert ex.entropy_bits({"a": Fraction(1, 2), "b": Fraction(1, 2)}) == pytest.approx(1.0)
    uniform = {i: Fraction(1, 8) for i in range(8)}
    assert ex.entropy_bits(uniform) == pytest.approx(3.0)


def test_huffman_dyadic_source_is_optimal():
    probs = {"a": Fraction(1, 2), "b": Fraction(1, 4), "c": Fraction(1, 8), "d": Fraction(1, 8)}
    lengths = ex.huffman_lengths(probs)
    assert lengths == {"a": 1, "b": 2, "c": 3, "d": 3}
    assert ex.expected_length(probs, lengths) == Fraction(7, 4)
    assert ex.entropy_bits(probs) == pytest.approx(1.75)
    assert ex.kraft_sum(lengths) == 1


def test_huffman_on_text_satisfies_bounds():
    probs = ex.frequencies(ex.TEXT)
    lengths = ex.huffman_lengths(probs)
    h = ex.entropy_bits(probs)
    big_l = float(ex.expected_length(probs, lengths))
    assert h <= big_l < h + 1
    assert ex.kraft_sum(lengths) == 1  # Huffman trees are full binary trees


def test_shannon_lengths():
    probs = {"a": Fraction(1, 3), "b": Fraction(2, 3)}
    assert ex.shannon_lengths(probs) == {"a": 2, "b": 1}
    probs = ex.frequencies(ex.TEXT)
    shan = ex.shannon_lengths(probs)
    assert ex.kraft_sum(shan) <= 1
    for s, p in probs.items():
        assert shan[s] == math.ceil(-math.log2(p) - 1e-12)


def test_pairs_reduce_overhead():
    probs = ex.frequencies("aaab")
    single = float(ex.expected_length(probs, ex.huffman_lengths(probs)))
    pairs = ex.pair_probs(probs)
    double = float(ex.expected_length(pairs, ex.huffman_lengths(pairs))) / 2
    h = ex.entropy_bits(probs)
    assert h <= double < single
    assert ex.huffman_lengths({"x": Fraction(1)}) == {"x": 1}
