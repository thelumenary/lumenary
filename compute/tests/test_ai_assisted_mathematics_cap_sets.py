import itertools
import random

import ai_assisted_mathematics_cap_sets as cs


def brute_force_is_cap(cap):
    """No three distinct points with x + y + z = 0 (mod 3), checked on all triples."""
    if len(set(cap)) != len(cap):
        return False
    for x, y, z in itertools.combinations(cap, 3):
        if all((a + b + c) % 3 == 0 for a, b, c in zip(x, y, z)):
            return False
    return True


def test_points_and_third_point():
    assert len(cs.points(3)) == 27
    assert cs.points(1) == [(0,), (1,), (2,)]
    for x, y in itertools.combinations(cs.points(2), 2):
        z = cs.third_point(x, y)
        assert z not in (x, y)  # distinct points determine a third, distinct point
        assert all((a + b + c) % 3 == 0 for a, b, c in zip(x, y, z))
        assert cs.third_point(x, z) == y  # the line is symmetric


def test_verifier_matches_brute_force():
    rng = random.Random(5)
    pts = cs.points(3)
    for _ in range(300):
        cap = rng.sample(pts, rng.randrange(1, 12))
        assert cs.is_cap_set(cap) == brute_force_is_cap(cap)
    assert not cs.is_cap_set([(0, 0), (0, 1), (0, 2)])  # a line
    assert not cs.is_cap_set([(0, 0), (0, 0)])  # repeated point
    assert cs.is_cap_set([(0, 0), (0, 1), (1, 0), (1, 1)])


def test_greedy_always_returns_a_maximal_cap():
    rng = random.Random(9)
    for n in (2, 3, 4):
        pts = cs.points(n)
        for _ in range(20):
            order = pts[:]
            rng.shuffle(order)
            cap = cs.greedy_cap(order)
            assert cs.is_cap_set(cap)
            # maximal: every other point would create a line
            for p in pts:
                if p not in cap:
                    assert not cs.is_cap_set(cap + [p])


def test_evolution_never_loses_ground_and_reaches_small_maxima():
    rng = random.Random(2023)
    for n in (2, 3, 4):
        cap, history = cs.evolve(n, rng, generations=400)
        assert cs.is_cap_set(cap)
        assert history == sorted(history)  # (1 + lambda): the best never gets worse
        assert len(cap) == history[-1] <= cs.KNOWN_MAXIMUM[n]
        assert len(cap) == cs.KNOWN_MAXIMUM[n]


def test_known_maxima_are_upper_bounds_for_search():
    rng = random.Random(1)
    cap, history = cs.evolve(5, rng, generations=20)
    assert cs.is_cap_set(cap)
    assert len(cap) <= cs.KNOWN_MAXIMUM[5] == 45
