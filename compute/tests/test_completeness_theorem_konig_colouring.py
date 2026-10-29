import completeness_theorem_konig_colouring as kc


def test_levels_of_a_path_with_two_colours():
    # D = {1}: the path 0 - 1 - 2 - ...; exactly two proper 2-colourings per level.
    tree = kc.levels(6, 2, (1,))
    assert [len(t) for t in tree] == [1, 2, 2, 2, 2, 2, 2]
    assert (0, 1, 0, 1, 0, 1) in tree[6]


def test_finite_obstruction_for_d_134():
    tree = kc.levels(9, 3, (1, 3, 4))
    sizes = [len(t) for t in tree]
    assert sizes[:8] == [1, 3, 6, 12, 18, 12, 6, 0]
    assert kc.surviving_branch(tree) is None
    # With 4 colours the same graph can be coloured greedily: no dead ends.
    assert set(kc.dead_ends(kc.levels(12, 4, (1, 3, 4)))) == {0}


def test_every_node_is_a_proper_colouring_and_extends_its_parent():
    tree = kc.levels(10, 4, (2, 3, 5, 7))
    for n, level in enumerate(tree):
        assert all(len(c) == n and kc.is_proper(c, (2, 3, 5, 7)) for c in level)
    parents = set(tree[9])
    assert all(c[:9] in parents for c in tree[10])


def test_dead_ends_and_surviving_branch_for_primes_below_ten():
    tree = kc.levels(24, 4, (2, 3, 5, 7))
    dead = kc.dead_ends(tree)
    assert dead[7:11] == [192, 96, 48, 24]
    assert sum(dead) == 360
    branch = kc.surviving_branch(tree)
    assert branch == tuple(n % 4 for n in range(24))
    assert all(len(t) == 24 for t in tree[11:])


def test_is_proper():
    assert kc.is_proper((0, 1, 2, 0, 1, 2), (1, 2))
    assert not kc.is_proper((0, 1, 0), (2,))
    assert kc.is_proper((), (1,))
