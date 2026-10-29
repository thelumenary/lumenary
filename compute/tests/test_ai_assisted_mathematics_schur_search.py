import itertools
import random

import ai_assisted_mathematics_schur_search as ss

# A Schur 3-colouring of {1, ..., 13}: classes {1, 4, 10, 13}, {2, 3, 11, 12}, {5, ..., 9}.
KNOWN = [0, 0, 1, 1, 0, 2, 2, 2, 2, 2, 0, 1, 1, 0]


def brute_force_is_schur(colouring):
    n = len(colouring) - 1
    return not any(
        colouring[x] == colouring[y] == colouring[x + y]
        for x in range(1, n + 1)
        for y in range(1, n + 1)
        if x + y <= n
    )


def test_verifier_accepts_known_colouring_and_rejects_bad_ones():
    assert ss.is_schur_colouring(KNOWN)
    assert ss.monochromatic_triples(KNOWN) == []
    bad = KNOWN[:]
    bad[2] = 0  # 1 + 1 = 2 with 1 and 2 both coloured 0
    assert (1, 1, 2) in ss.monochromatic_triples(bad)
    assert not ss.is_schur_colouring(bad)
    assert not ss.is_schur_colouring([0, 0, 0])  # 1 + 1 = 2


def test_verifier_agrees_with_brute_force_on_random_colourings():
    rng = random.Random(7)
    for _ in range(300):
        n = rng.randrange(1, 15)
        colouring = [0] + [rng.randrange(3) for _ in range(n)]
        assert ss.is_schur_colouring(colouring) == brute_force_is_schur(colouring)


def test_conflicts_at_counts_triples_through_z():
    rng = random.Random(11)
    for _ in range(100):
        n = rng.randrange(2, 16)
        colouring = [0] + [rng.randrange(3) for _ in range(n)]
        z = rng.randrange(1, n + 1)
        before = colouring[:]
        for c in range(3):
            trial = colouring[:]
            trial[z] = c
            expected = sum(1 for t in ss.monochromatic_triples(trial) if z in t)
            assert ss.conflicts_at(colouring, z, c) == expected
            assert colouring == before  # the probe restores the colouring


def test_local_search_returns_verified_colourings():
    rng = random.Random(1)
    for n, k in [(4, 2), (10, 3), (13, 3), (25, 4)]:
        colouring, steps = ss.local_search(n, k, rng)
        assert colouring is not None and len(colouring) == n + 1
        assert ss.is_schur_colouring(colouring)
        assert max(colouring[1:]) < k
    impossible, steps = ss.local_search(5, 2, rng, max_steps=200)
    assert impossible is None and steps == 200


def test_exhaustive_schur_numbers():
    assert [ss.schur_number(k) for k in (1, 2, 3)] == [1, 4, 13]
    assert ss.exhaustive_schur(2, 4) == [[0, 0, 1, 1, 0]]
    assert ss.exhaustive_schur(2, 5) == []
    assert ss.exhaustive_schur(3, 14) == []
    assert all(ss.is_schur_colouring(c) for c in ss.exhaustive_schur(3, 13))
    assert len(ss.exhaustive_schur(3, 13)) == 3


def test_triangle_free_lift():
    assert ss.triangle_free_lift(KNOWN) == 0
    # The lift of a non-Schur colouring has a monochromatic triangle.
    bad = KNOWN[:]
    bad[2] = 0
    assert ss.triangle_free_lift(bad) > 0
    # For two colours the lift of [1, 4], [2, 3] is the pentagon and its complement.
    pentagon = [0, 0, 1, 1, 0]
    assert ss.triangle_free_lift(pentagon) == 0
    edges = [(i, j) for i, j in itertools.combinations(range(5), 2) if pentagon[j - i] == 0]
    assert len(edges) == 5


def test_classes_partition():
    parts = ss.classes(KNOWN, 3)
    assert parts == [[1, 4, 10, 13], [2, 3, 11, 12], [5, 6, 7, 8, 9]]
    assert sorted(x for p in parts for x in p) == list(range(1, 14))
