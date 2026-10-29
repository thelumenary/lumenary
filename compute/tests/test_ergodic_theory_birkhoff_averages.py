import math
import random
from fractions import Fraction

import pytest

import ergodic_theory_birkhoff_averages as eb


def test_irrational_rotation_average_approaches_length():
    assert eb.rotation_average(eb.GOLDEN, 0.0, 100_000) == pytest.approx(0.25, abs=1e-3)
    assert eb.rotation_average(math.sqrt(2) % 1, 0.1, 50_000, 0.2, 0.7) == pytest.approx(0.5, abs=1e-3)


def test_rational_rotation_depends_on_start():
    assert eb.rotation_average(0.4, 0.0, 1000) == pytest.approx(0.4)
    assert eb.rotation_average(0.4, 0.3, 1000) == pytest.approx(0.2)


def test_rotation_overlap_formula_and_non_mixing():
    assert eb.rotation_overlap(0.5, 1) == pytest.approx(0.0)
    assert eb.rotation_overlap(0.25, 4) == pytest.approx(0.5)
    fib = [55, 89, 144, 233]
    assert all(eb.rotation_overlap(eb.GOLDEN, n) > 0.49 for n in fib)
    assert eb.rotation_overlap(eb.GOLDEN, 4) < 0.05


def test_float_doubling_collapses():
    assert eb.float_doubling_steps(0.0) == 0
    assert eb.float_doubling_steps(0.5) == 1
    assert 50 <= eb.float_doubling_steps(0.1) <= 60


def test_exact_doubling_reads_binary_digits():
    bits = [0, 1, 1, 0, 0, 0, 1, 0]
    assert eb.exact_doubling_frequency(bits) == bits.count(0) / len(bits)
    rng = random.Random(7)
    many = [rng.randrange(2) for _ in range(2000)]
    assert eb.exact_doubling_frequency(many) == pytest.approx(0.5, abs=0.05)


def test_continued_fraction_digits():
    assert eb.continued_fraction_digits(Fraction(3, 7), 10) == [2, 3]
    assert eb.continued_fraction_digits(Fraction(13, 21), 10) == [1, 1, 1, 1, 1, 2]
    assert eb.continued_fraction_digits(Fraction(0), 5) == []


def test_gauss_kuzmin_is_a_probability_distribution():
    total = sum(eb.gauss_kuzmin(k) for k in range(1, 200_000))
    assert total == pytest.approx(1.0, abs=1e-5)
    assert eb.gauss_kuzmin(1) == pytest.approx(math.log2(4 / 3))


def test_gauss_measure_invariance_partial_products():
    for t in [0.1, 0.5, 0.9]:
        assert eb.gauss_preimage_measure(t, 20_000) == pytest.approx(math.log2(1 + t), abs=1e-4)
