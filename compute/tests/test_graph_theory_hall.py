import random

import graph_theory_hall as gh


def test_matching_is_valid_and_maximum_on_examples():
    adj = [frozenset({0, 1}), frozenset({0}), frozenset({1, 2})]
    match = gh.maximum_matching(adj)
    assert len(match) == 3
    assert all(j in adj[i] for j, i in match.items())
    assert len(set(match.values())) == len(match)


def test_hall_violator_detection():
    adj = [frozenset({0}), frozenset({0}), frozenset({1, 2})]
    assert gh.hall_violator(adj) == (0, 1)
    assert len(gh.maximum_matching(adj)) == 2
    assert gh.max_deficiency(adj) == 1


def test_hall_equivalence_and_konig_on_random_graphs():
    rng = random.Random(7)
    for _ in range(150):
        adj = gh.random_bipartite(4, 5, rng.random(), rng)
        m = len(gh.maximum_matching(adj))
        assert (gh.hall_violator(adj) is None) == (m == 4)
        assert m == 4 - gh.max_deficiency(adj)
        assert m == gh.min_vertex_cover(adj, 5)


def test_neighbourhood_and_empty_graph():
    adj = [frozenset(), frozenset({2}), frozenset({2, 3})]
    assert gh.neighbourhood(adj, (1, 2)) == {2, 3}
    assert gh.hall_violator(adj) == (0,)
    empty = [frozenset() for _ in range(3)]
    assert gh.maximum_matching(empty) == {}
    assert gh.min_vertex_cover(empty, 3) == 0


def test_complete_bipartite_graph():
    adj = [frozenset(range(3)) for _ in range(3)]
    assert len(gh.maximum_matching(adj)) == 3
    assert gh.min_vertex_cover(adj, 3) == 3
