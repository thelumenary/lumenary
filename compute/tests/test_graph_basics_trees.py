import graph_basics_trees as gt


def test_components_and_cycles():
    assert gt.components(4, [(0, 1), (2, 3)]) == 2
    assert gt.components(3, []) == 3
    assert gt.has_cycle(3, [(0, 1), (1, 2), (2, 0)])
    assert not gt.has_cycle(4, [(0, 1), (1, 2), (1, 3)])


def test_tree_census_matches_cayley():
    for n in range(2, 7):
        total, conn, acyc, trees = gt.tree_census(n)
        assert conn == acyc == len(trees) == n ** (n - 2)


def test_canonical_code_classes():
    expected = {2: 1, 3: 1, 4: 2, 5: 3, 6: 6}
    for n, classes in expected.items():
        trees = gt.tree_census(n)[3]
        assert len({gt.canonical_tree(n, t) for t in trees}) == classes


def test_canonical_code_separates_path_and_star():
    path = [(0, 1), (1, 2), (2, 3)]
    star = [(0, 1), (0, 2), (0, 3)]
    relabelled_path = [(2, 0), (0, 3), (3, 1)]
    assert gt.canonical_tree(4, path) != gt.canonical_tree(4, star)
    assert gt.canonical_tree(4, path) == gt.canonical_tree(4, relabelled_path)


def test_find_isomorphism():
    pentagon = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    pentagram = [(0, 2), (2, 4), (4, 1), (1, 3), (3, 0)]
    perm = gt.find_isomorphism(5, pentagon, pentagram)
    assert perm is not None
    image = {frozenset((perm[a], perm[b])) for a, b in pentagon}
    assert image == {frozenset(e) for e in pentagram}
    path = [(0, 1), (1, 2), (2, 3)]
    star = [(0, 1), (0, 2), (0, 3)]
    assert gt.find_isomorphism(4, path, star) is None
