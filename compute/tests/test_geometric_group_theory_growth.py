import geometric_group_theory_growth as g


def test_z2_balls_are_quadratic():
    sizes = g.ball_sizes((0, 0), g.Z2_GENERATORS, g.z2_mul, 10)
    assert sizes == [2 * r * r + 2 * r + 1 for r in range(11)]


def test_sanov_ball_matches_free_group():
    sizes = g.ball_sizes((1, 0, 0, 1), g.SANOV_GENERATORS, g.mat_mul, 7)
    assert sizes == [2 * 3 ** r - 1 for r in range(8)]


def test_generators_are_closed_under_inverses():
    identity = (1, 0, 0, 1)
    for s in g.SANOV_GENERATORS:
        assert any(g.mat_mul(s, t) == identity for t in g.SANOV_GENERATORS)
    for s in g.HEIS_GENERATORS:
        assert any(g.heis_mul(s, t) == (0, 0, 0) for t in g.HEIS_GENERATORS)


def test_heisenberg_is_non_commutative_with_central_commutator():
    x, y = (1, 0, 0), (0, 1, 0)
    xinv, yinv = (-1, 0, 0), (0, -1, 0)
    comm = g.heis_mul(g.heis_mul(g.heis_mul(x, y), xinv), yinv)
    assert comm == (0, 0, 1)
    assert g.heis_mul(comm, x) == g.heis_mul(x, comm)


def test_non_free_matrices_collapse_balls():
    # A = [[1, 1], [0, 1]] and B = [[1, 0], [1, 1]] generate SL(2, Z), which is
    # not free: (A B^-1 A)^4 = 1, so the balls are smaller than in the tree.
    gens = [(1, 1, 0, 1), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, -1, 1)]
    sizes = g.ball_sizes((1, 0, 0, 1), gens, g.mat_mul, 8)
    assert sizes[8] < 2 * 3 ** 8 - 1


def test_growth_degree_estimates():
    heis = g.ball_sizes((0, 0, 0), g.HEIS_GENERATORS, g.heis_mul, 12)
    z2 = g.ball_sizes((0, 0), g.Z2_GENERATORS, g.z2_mul, 12)
    assert 3.8 < g.growth_degree(heis, 6) < 4.1
    assert 1.8 < g.growth_degree(z2, 6) < 2.0
