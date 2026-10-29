import itertools
import math

import additive_extremal_combinatorics_turan_ramsey as tr


def test_edge_bits_and_clique_masks():
    bits = tr.edge_bits(4)
    assert len(bits) == 6 and bits[(0, 1)] == 0
    tri = tr.clique_masks(4, 3, bits)
    assert len(tri) == 4
    assert all(bin(m).count("1") == 3 for m in tri)
    assert tr.clique_masks(4, 4, bits) == [(1 << 6) - 1]


def test_turan_numbers():
    assert tr.turan_part_sizes(7, 3) == [2, 2, 3]
    assert tr.turan_edges(6, 2) == 9
    assert tr.turan_edges(6, 3) == 12
    assert tr.turan_edges(7, 3) == 16
    # Turan's bound (1 - 1/r) n^2 / 2
    for n in range(1, 15):
        for r in range(1, 6):
            assert tr.turan_edges(n, r) <= (1 - 1 / r) * n * n / 2 + 1e-9


def test_mantel_and_turan_exhaustively_on_five_vertices():
    best, graphs = tr.extremal_graphs(5, 2)
    assert best == 6  # floor(25 / 4)
    bits = tr.edge_bits(5)
    assert {tuple(tr.non_adjacency_classes(g, 5, bits)) for g in graphs} == {(2, 3)}
    assert len(graphs) == math.comb(5, 2)  # choose the part of size 2


def test_non_adjacency_classes_rejects_non_multipartite():
    bits = tr.edge_bits(4)
    path = (1 << bits[(0, 1)]) | (1 << bits[(1, 2)]) | (1 << bits[(2, 3)])
    assert tr.non_adjacency_classes(path, 4, bits) is None
    complete = (1 << 6) - 1
    assert tr.non_adjacency_classes(complete, 4, bits) == [1, 1, 1, 1]


def test_paley_graph_17():
    adj = tr.paley_graph(17)
    assert all(len(a) == 8 for a in adj)
    assert all(x not in adj[x] for x in range(17))
    assert all((y in adj[x]) == (x in adj[y]) for x in range(17) for y in range(17))
    assert tr.homogeneous_sets(adj, 4) == 0
    assert tr.homogeneous_sets(adj, 3) > 0


def test_paley_graph_5_is_the_pentagon():
    adj = tr.paley_graph(5)
    assert adj[0] == {1, 4}
    assert tr.homogeneous_sets(adj, 3) == 0  # R(3, 3) > 5


def test_ramsey_bounds():
    assert [tr.erdos_bound(k) for k in range(4, 8)] == [6, 11, 17, 27]
    for k in range(4, 11):
        n = tr.erdos_bound(k)
        assert math.comb(n, k) * 2 < 2 ** math.comb(k, 2)
        assert math.comb(n + 1, k) * 2 >= 2 ** math.comb(k, 2)
        assert tr.erdos_bound(k) < math.comb(2 * k - 2, k - 1)
    assert tr.deletion_bound(10) > tr.erdos_bound(10)
