import math

import algorithms_and_efficiency_search_race as sr


def test_binary_search_finds_present_and_rejects_absent():
    n = 50
    for i in range(n):
        idx, probes = sr.binary_search(sr.evens, n, 2 * i)
        assert idx == i and 1 <= probes <= 6
    for t in (-1, 1, 51, 99, 100):
        assert sr.binary_search(sr.evens, n, t)[0] is None


def test_binary_search_on_a_real_list_with_repeats():
    a = [1, 3, 3, 3, 8, 13, 21]
    idx, _ = sr.binary_search(lambda i: a[i], len(a), 3)
    assert a[idx] == 3
    assert sr.binary_search(lambda i: a[i], len(a), 4)[0] is None
    assert sr.binary_search(lambda i: a[i], 0, 4) == (None, 0)


def test_worst_case_matches_log_bound():
    for n in range(1, 130):
        assert sr.worst_binary_probes(n) == math.floor(math.log2(n)) + 1
    assert sr.worst_binary_probes(1000) == 10


def test_target_beyond_end_is_a_worst_case():
    for n in (1, 2, 3, 10, 64, 1000, 10**6):
        assert sr.binary_search(sr.evens, n, 2 * n)[1] == n.bit_length()


def test_linear_search_counts():
    assert sr.linear_search(sr.evens, 10, 6) == (3, 4)
    assert sr.linear_search(sr.evens, 10, 7) == (None, 10)
    assert sr.linear_search(sr.evens, 0, 0) == (None, 0)


def test_log2_floor_exact():
    assert [sr.log2_floor(n) for n in (1, 2, 3, 4, 7, 8, 1023, 1024)] == [0, 1, 1, 2, 2, 3, 9, 10]
    assert sr.log2_floor(10**12) == 39
