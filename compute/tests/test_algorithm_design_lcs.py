import itertools

import algorithm_design_lcs as adl


def brute_lcs(x, y):
    """Longest common subsequence length by trying all subsequences of x."""
    for k in range(len(x), -1, -1):
        for idx in itertools.combinations(range(len(x)), k):
            s = "".join(x[i] for i in idx)
            if adl.is_subsequence(s, y):
                return k
    return 0


def test_classic_example():
    t = adl.lcs_table("ABCBDAB", "BDCABA")
    assert t[-1][-1] == 4
    z = adl.traceback("ABCBDAB", "BDCABA", t)
    assert len(z) == 4 and adl.is_subsequence(z, "ABCBDAB") and adl.is_subsequence(z, "BDCABA")


def test_edge_cases():
    assert adl.lcs_table("", "ABC")[-1][-1] == 0
    assert adl.traceback("ABC", "", adl.lcs_table("ABC", "")) == ""
    assert adl.lcs_table("ACGT", "ACGT")[-1][-1] == 4


def test_is_subsequence():
    assert adl.is_subsequence("ACE", "ABCDE")
    assert not adl.is_subsequence("AEC", "ABCDE")
    assert adl.is_subsequence("", "")


def test_table_matches_brute_force():
    words = ["", "A", "AB", "BA", "ACGT", "GATTACA", "TAGCAT"]
    for x in words:
        for y in words:
            assert adl.lcs_table(x, y)[-1][-1] == brute_lcs(x, y)


def test_naive_recursion_agrees_and_costs_more():
    length, calls = adl.naive_calls("GATTACA", "TAGCAT")
    assert length == adl.lcs_table("GATTACA", "TAGCAT")[-1][-1]
    assert calls > (7 + 1) * (6 + 1)
    assert adl.naive_calls("", "A") == (0, 1)
