from itertools import permutations
from math import factorial

import counting_principles_brute_force as cb


def test_ordered_selections():
    assert cb.ordered_selections(10, 4) == 5040
    assert cb.ordered_selections(8, 3) == 336
    assert cb.ordered_selections(5, 5) == factorial(5)
    assert cb.ordered_selections(5, 0) == 1
    assert cb.ordered_selections(3, 4) == 0


def test_ordered_selections_match_listing():
    for n in range(0, 7):
        for k in range(0, n + 2):
            assert cb.ordered_selections(n, k) == sum(1 for _ in permutations(range(n), k))


def test_pin_counts_and_complement():
    total = cb.count_pins()
    distinct = cb.count_pins(repeats_allowed=False)
    assert total == 10000
    assert distinct == 10 * 9 * 8 * 7
    assert total - distinct == 4960


def test_codes_with_a_digit_by_complement():
    for length in (1, 2, 3):
        assert cb.count_codes_with_digit(length) == 36 ** length - 26 ** length


def test_overlap_rule():
    assert cb.count_divisible_by_either(100, 2, 5) == 50 + 20 - 10
    assert cb.count_divisible_by_either(60, 2, 3) == 30 + 20 - 10
    assert cb.count_divisible_by_either(21, 3, 7) == 7 + 3 - 1


def test_repeated_letters_reduce_the_count():
    assert len(set(permutations("LETTER"))) == factorial(6) // (2 * 2)
