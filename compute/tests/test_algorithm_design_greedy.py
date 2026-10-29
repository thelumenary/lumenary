import itertools
import random

import pytest

import algorithm_design_greedy as adg


def test_kruskal_small_examples():
    # a triangle: the MST drops the heaviest edge
    assert adg.kruskal(3, [(1, 0, 1), (2, 1, 2), (5, 0, 2)]) == 3
    with pytest.raises(ValueError):
        adg.kruskal(3, [(1, 0, 1)])


def test_kruskal_matches_brute_force():
    rng = random.Random(11)
    for _ in range(50):
        edges = [(rng.randint(1, 5), u, v) for u, v in itertools.combinations(range(5), 2)]
        assert adg.kruskal(5, edges) == adg.brute_force_mst(5, edges)


def test_dijkstra_correct_on_nonnegative_dags():
    rng = random.Random(5)
    for _ in range(100):
        g = adg.random_dag(6, rng, 0, 9)
        assert adg.dijkstra(6, g) == adg.bellman_ford(6, g)


def test_dijkstra_fails_with_negative_edge():
    adj = [[(1, 1), (2, 2)], [], [(1, -2)]]
    assert adg.dijkstra(3, adj)[1] == 1
    assert adg.bellman_ford(3, adj)[1] == 0


def test_unreachable_vertices():
    adj = [[(1, 3)], [], []]
    assert adg.dijkstra(3, adj) == [0, 3, None]
    assert adg.bellman_ford(3, adj) == [0, 3, None]


def test_coins():
    assert adg.greedy_coins((1, 3, 4), 6) == 3
    assert adg.optimal_coins((1, 3, 4), 6)[6] == 2
    assert adg.first_greedy_failure((1, 3, 4)) == 6
    assert adg.first_greedy_failure((1, 5, 10)) is None
    assert adg.first_greedy_failure((1, 2, 5)) is None
    # brute-force check of the DP on small amounts
    best = adg.optimal_coins((1, 4, 6), 20)
    for x in range(21):
        brute = min(i + j + k for i in range(21) for j in range(6) for k in range(4)
                    if i + 4 * j + 6 * k == x)
        assert best[x] == brute
