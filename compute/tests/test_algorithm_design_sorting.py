import itertools
import math
import random

import algorithm_design_sorting as ads


def test_sorts_are_correct():
    rng = random.Random(1)
    for n in range(0, 30):
        items = [rng.randint(0, 9) for _ in range(n)]
        assert ads.merge_sort(items)[0] == sorted(items)
        assert ads.insertion_sort(items)[0] == sorted(items)


def test_insertion_sort_extremes():
    assert ads.insertion_sort(list(range(10)))[1] == 9  # already sorted: n - 1
    assert ads.insertion_sort(list(range(10, 0, -1)))[1] == 45  # reversed: n(n-1)/2


def test_merge_worst_case_matches_recurrence():
    for n in range(1, 8):
        assert ads.worst_case(ads.merge_sort, n) == ads.merge_recurrence(n)


def test_recurrence_bound_n_ceil_log():
    for n in range(2, 300):
        assert ads.merge_recurrence(n) <= n * math.ceil(math.log2(n))
    assert ads.merge_recurrence(1024) == 1024 * 10 - 1023


def test_lower_bound_values_and_validity():
    assert [ads.lower_bound(n) for n in range(1, 8)] == [0, 1, 3, 5, 7, 10, 13]
    for n in range(1, 8):
        assert ads.worst_case(ads.merge_sort, n) >= ads.lower_bound(n)
        assert ads.worst_case(ads.insertion_sort, n) >= ads.lower_bound(n)


def test_average_case_is_deterministic():
    a = ads.average_case(ads.merge_sort, 32, 5, random.Random(3))
    b = ads.average_case(ads.merge_sort, 32, 5, random.Random(3))
    assert a == b
    assert ads.average_case(ads.insertion_sort, 1, 3, random.Random(0)) == 0
