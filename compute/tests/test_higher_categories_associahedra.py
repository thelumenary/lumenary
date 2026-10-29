from math import comb

import pytest

import higher_categories_associahedra as ha


@pytest.mark.parametrize("n", range(1, 8))
def test_bracketings_are_catalan_and_distinct(n):
    trees = ha.bracketings(tuple("abcdefg"[:n]))
    assert len(trees) == comb(2 * (n - 1), n - 1) // n
    assert len(set(trees)) == len(trees)
    assert all(ha.leaves(t) == "abcdefg"[:n] for t in trees)


def test_show_and_combs():
    assert ha.show(ha.comb_bracketing(4, left=True)) == "((ab)c)d"
    assert ha.show(ha.comb_bracketing(4, left=False)) == "a(b(cd))"
    assert ha.show((("a", "b"), ("c", "d"))) == "(ab)(cd)"


def test_moves_are_associator_steps():
    t = (("a", "b"), "c")
    assert ha.moves(t) == [("a", ("b", "c"))]
    assert ha.moves(("a", ("b", "c"))) == [(("a", "b"), "c")]
    assert ha.moves(("a", ("b", "c")), forward_only=True) == []
    # Moves preserve the word and are symmetric.
    for v in ha.bracketings(tuple("abcde")):
        for w in ha.moves(v):
            assert ha.leaves(w) == "abcde"
            assert v in ha.moves(w)


@pytest.mark.parametrize("n", range(3, 8))
def test_edge_count_and_connectivity(n):
    vertices, edges = ha.associator_graph(n)
    # Each bracketing has n - 2 internal edges, each allowing exactly one move.
    assert len(edges) == (n - 2) * len(vertices) // 2
    nbrs = {v: set(ha.moves(v)) for v in vertices}
    assert all(len(nbrs[v]) == n - 2 for v in vertices)
    reach = ha.distances(vertices[0], nbrs.__getitem__)
    assert len(reach) == len(vertices)


def test_pentagon_paths():
    assert ha.directed_path_lengths(3) == [1]
    assert ha.directed_path_lengths(4) == [2, 3]
    lengths = ha.directed_path_lengths(5)
    # Shortest chain n - 2, longest chain (n-1)(n-2)/2 in the Tamari lattice.
    assert min(lengths) == 3 and max(lengths) == 6


def test_k5_faces_and_euler_characteristic():
    faces = ha.facets(5)
    sizes = sorted(len(f) for f in faces)
    assert sizes == [4, 4, 4, 5, 5, 5, 5, 5, 5]
    vertices, edges = ha.associator_graph(5)
    assert len(vertices) - len(edges) + len(faces) == 2
    assert ha.face_boundary_rank(5) == len(edges) - len(vertices) + 1 == 8


def test_gf2_rank():
    assert ha.gf2_rank([]) == 0
    assert ha.gf2_rank([0b011, 0b110, 0b101]) == 2
    assert ha.gf2_rank([1, 2, 4, 7]) == 3
