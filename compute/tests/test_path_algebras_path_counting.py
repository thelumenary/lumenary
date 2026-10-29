import path_algebras_path_counting as pc


def test_linear_a_n_dimension():
    for n in range(1, 8):
        a = pc.adjacency(n, [(i, i + 1) for i in range(n - 1)])
        assert pc.is_acyclic(a)
        assert sum(map(sum, pc.cartan(a))) == n * (n + 1) // 2


def test_cartan_counts_paths():
    a = pc.adjacency(3, [(0, 1), (1, 2), (0, 2)])
    assert pc.cartan(a) == [[1, 1, 2], [0, 1, 1], [0, 0, 1]]


def test_cycles_detected():
    assert not pc.is_acyclic(pc.adjacency(1, [(0, 0)]))
    assert not pc.is_acyclic(pc.adjacency(3, [(0, 1), (1, 2), (2, 0)]))
    assert pc.is_acyclic(pc.adjacency(2, [(0, 1), (0, 1)]))


def test_path_growth():
    assert pc.paths_by_length(pc.adjacency(1, [(0, 0), (0, 0)]), 5) == [1, 2, 4, 8, 16, 32]
    assert pc.paths_by_length(pc.adjacency(1, [(0, 0)]), 3) == [1, 1, 1, 1]
    assert pc.paths_by_length(pc.adjacency(2, [(0, 1), (0, 1)]), 3) == [2, 2, 0, 0]


def test_kronecker_dimension_four():
    a = pc.adjacency(2, [(0, 1), (0, 1)])
    assert pc.cartan(a) == [[1, 2], [0, 1]]
