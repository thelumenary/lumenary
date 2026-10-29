import itertools
import math
import random
from fractions import Fraction

import probabilistic_method_ramsey as pr


def test_expected_monochromatic_exact():
    assert pr.expected_monochromatic(6, 4) == Fraction(15, 32)
    assert pr.expected_monochromatic(5, 3) == Fraction(10, 4)


def test_first_moment_bound_beats_erdos_closed_form():
    for k in range(3, 12):
        n = pr.first_moment_bound(k)
        assert pr.expected_monochromatic(n, k) < 1
        assert pr.expected_monochromatic(n + 1, k) >= 1
        assert n >= math.floor(2 ** (k / 2))          # Erdos: R(k,k) > 2^(k/2)


def test_deletion_bound_at_least_first_moment():
    for k in range(3, 11):
        assert pr.deletion_bound(k) >= pr.first_moment_bound(k)


def test_counting_monochromatic():
    n = 5
    red = {e: True for e in itertools.combinations(range(n), 2)}
    assert pr.count_monochromatic(red, n, 3) == math.comb(5, 3)
    pentagon = {(i, j): (j - i) % 5 in (1, 4)
                for i, j in itertools.combinations(range(n), 2)}
    assert pr.count_monochromatic(pentagon, n, 3) == 0   # R(3,3) > 5


def test_paley_graph_17():
    paley = pr.paley_colouring(17)
    assert sum(paley.values()) == 68                      # 17 * 8 / 2 edges
    assert pr.count_monochromatic(paley, 17, 4) == 0
    assert pr.count_monochromatic(paley, 17, 3) > 0


def test_random_colouring_is_seeded_and_unbiased():
    a = pr.random_colouring(10, random.Random(5))
    b = pr.random_colouring(10, random.Random(5))
    assert a == b and len(a) == 45
    rng = random.Random(7)
    reds = sum(sum(pr.random_colouring(10, rng).values()) for _ in range(200))
    assert abs(reds / (200 * 45) - 0.5) < 0.02
