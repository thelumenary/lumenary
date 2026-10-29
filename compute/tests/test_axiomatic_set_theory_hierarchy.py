import pytest

import axiomatic_set_theory_hierarchy as h


def test_coding_round_trip():
    for code in range(300):
        assert h.from_members(h.members(code)) == code
    assert h.members(0) == []
    assert h.members(11) == [0, 1, 3]
    with pytest.raises(ValueError):
        h.members(-1)


def test_stage_sizes_and_stages():
    assert h.stage_sizes(5) == [0, 1, 2, 4, 16, 65536]
    for k in range(5):
        assert h.stage(k) == list(range(h.stage_sizes(k)[k]))


def test_rank_matches_stages():
    sizes = h.stage_sizes(5)
    for code in range(sizes[5]):
        r = h.rank(code)
        assert code < sizes[r + 1]
        assert r == 0 or code >= sizes[r]
    assert [h.rank(h.von_neumann(n)) for n in range(5)] == [0, 1, 2, 3, 4]


def test_von_neumann_codes():
    assert [h.von_neumann(n) for n in range(5)] == [0, 1, 3, 11, 2059]
    # n + 1 = n U {n}
    for n in range(4):
        assert h.members(h.von_neumann(n + 1)) == sorted(h.members(h.von_neumann(n)) + [h.von_neumann(n)])
        assert h.is_transitive(h.von_neumann(n))


def test_transitivity_and_foundation():
    assert not h.is_transitive(h.from_members([1]))  # {{0}} lacks 0
    assert all(h.has_minimal_member(c) for c in range(1, 5000))
    assert not h.has_minimal_member(0)


def test_show():
    assert h.show(0) == "{}"
    assert h.show(1) == "{{}}"
    assert h.show(10) == "{{{}}, {{}, {{}}}}"


def test_ranks_below_agrees_with_recursive_rank():
    ranks = h.ranks_below(5000)
    assert all(ranks[c] == h.rank(c) for c in range(5000))
