import random

import path_algebras_barcodes as pb


def test_inverse_and_rank():
    rng = random.Random(4)
    for n in range(1, 5):
        g = pb.random_invertible(n, rng)
        ident = [[int(i == j) for j in range(n)] for i in range(n)]
        assert pb.matmul(g, pb.inverse(g)) == ident
        assert pb.rank(g) == n
    assert pb.rank([[1, 2], [2, 4]]) == 1
    assert pb.rank([[7, 0]]) == 0


def test_interval_sum_dimensions_and_maps():
    dims, maps = pb.interval_sum(3, [(1, 2), (2, 3)])
    assert dims == [1, 2, 1]
    assert maps[0] == [[1], [0]]          # V_1 -> V_2 hits the first interval
    assert maps[1] == [[0, 1]]            # V_2 -> V_3 keeps the second


def test_single_interval_multiplicities():
    dims, maps = pb.interval_sum(4, [(2, 3)])
    mult = pb.multiplicities(dims, maps)
    assert mult[(2, 3)] == 1
    assert sum(mult.values()) == 1


def test_recovery_after_disguise():
    rng = random.Random(11)
    for _ in range(40):
        n = rng.randint(2, 5)
        intervals = [tuple(sorted(rng.choices(range(1, n + 1), k=2)))
                     for _ in range(rng.randint(1, 5))]
        dims, maps = pb.interval_sum(n, intervals)
        hidden = pb.disguise(dims, maps, rng)
        mult = pb.multiplicities(dims, hidden)
        assert all(v >= 0 for v in mult.values())
        for (i, j), v in mult.items():
            assert v == intervals.count((i, j))


def test_composite_rank_boundaries():
    dims, maps = pb.interval_sum(3, [(1, 3)])
    assert pb.composite_rank(dims, maps, 1, 3) == 1
    assert pb.composite_rank(dims, maps, 0, 2) == 0
    assert pb.composite_rank(dims, maps, 2, 4) == 0
