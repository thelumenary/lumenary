import math
import random
from itertools import permutations

import algorithms_and_efficiency_sorting_counts as sc


def test_sorts_are_correct():
    rng = random.Random(7)
    for n in range(0, 30):
        data = [rng.randint(0, 9) for _ in range(n)]
        assert sc.insertion_sort(data)[0] == sorted(data)
        assert sc.merge_sort(data)[0] == sorted(data)


def test_insertion_sort_extremes():
    for n in range(1, 12):
        assert sc.insertion_sort(range(n))[1] == n - 1            # already sorted
        assert sc.insertion_sort(range(n, 0, -1))[1] == n * (n - 1) // 2  # reversed


def test_worst_cases_small_n():
    assert [sc.worst_case(sc.insertion_sort, n) for n in range(1, 8)] == [0, 1, 3, 6, 10, 15, 21]
    assert [sc.worst_case(sc.merge_sort, n) for n in range(1, 8)] == [0, 1, 3, 5, 8, 11, 14]


def test_lower_bound_values_and_validity():
    assert [sc.lower_bound(n) for n in range(1, 8)] == [0, 1, 3, 5, 7, 10, 13]
    for n in range(1, 13):
        assert 2 ** sc.lower_bound(n) >= math.factorial(n) > 2 ** (sc.lower_bound(n) - 1) or n == 1
    # No method beats the bound: both worst cases sit at or above it.
    for n in range(1, 7):
        assert sc.worst_case(sc.merge_sort, n) >= sc.lower_bound(n)


def test_comparison_counts_are_permutation_independent_of_values():
    # Only the relative order matters: relabelling values keeps the count.
    for p in permutations(range(5)):
        q = [10 * x + 3 for x in p]
        assert sc.insertion_sort(p)[1] == sc.insertion_sort(q)[1]
        assert sc.merge_sort(p)[1] == sc.merge_sort(q)[1]
