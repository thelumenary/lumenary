import random
from fractions import Fraction

import axiom_of_choice_finite_zorn as az


def test_span_and_independence():
    assert az.span([]) == {0}
    assert az.span([1, 2]) == {0, 1, 2, 3}
    assert az.independent([1, 2, 4, 8])
    assert not az.independent([1, 2, 3])
    assert not az.independent([5, 5])


def test_greedy_extension_always_reaches_a_basis():
    rng = random.Random(3)
    vectors = list(range(1, 16))
    for _ in range(100):
        start = rng.sample(vectors, 2)
        if not az.independent(start):
            continue
        order = vectors[:]
        rng.shuffle(order)
        result = az.extend_to_maximal(start, order)
        assert result[: len(start)] == start
        assert az.independent(result) and len(result) == 4


def test_number_of_bases_matches_the_formula():
    # (2^n - 1)(2^n - 2)...(2^n - 2^(n-1)) / n!
    assert az.count_bases(4) == 15 * 14 * 12 * 8 // 24 == 840
    assert az.count_bases(3) == 7 * 6 * 4 // 6 == 28
    assert az.count_bases(2) == 3


def test_maximal_ideals_are_generated_by_prime_divisors():
    for n in range(2, 61):
        assert az.maximal_ideal_generators(n) == az.prime_divisors(n)
    assert az.ideal(4, 12) == frozenset({0, 4, 8})
    assert az.prime_divisors(360) == [2, 3, 5]
    assert az.prime_divisors(97) == [97]


def test_calkin_wilf_order():
    seq = az.calkin_wilf(15)
    assert seq[:7] == [Fraction(1), Fraction(1, 2), Fraction(2), Fraction(1, 3),
                       Fraction(3, 2), Fraction(2, 3), Fraction(3)]
    long = az.calkin_wilf(4095)
    assert len(set(long)) == len(long), "no rational is repeated"
    assert all(x > 0 for x in long)
    # 1/12 sits at depth 11 of the Calkin-Wilf tree, the last row we listed.
    assert Fraction(1, 12) in long and Fraction(1, 13) not in long
