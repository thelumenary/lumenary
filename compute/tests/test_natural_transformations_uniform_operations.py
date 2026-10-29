from itertools import permutations

import natural_transformations_uniform_operations as nt


def test_counts_of_tables_and_maps():
    assert sum(1 for _ in nt.all_tables(2)) == 16
    assert sum(1 for _ in nt.all_tables(3)) == 3 ** 9
    assert len(nt.all_maps(2, 3)) == 9
    assert len(nt.all_maps(3, 2)) == 8
    assert nt.all_maps(0, 4) == [()]


def test_projections_are_natural_for_every_map_between_sizes():
    for k in (0, 1):
        for m in (1, 2, 3):
            for n in (1, 2, 3):
                src, dst = nt.projection(m, k), nt.projection(n, k)
                assert all(nt.commutes(src, dst, f, m, n)
                           for f in nt.all_maps(m, n))


def test_only_projections_commute_with_all_self_maps():
    for n in (2, 3):
        found = set(nt.natural_tables(n, nt.all_maps(n, n)))
        assert found == {nt.projection(n, 0), nt.projection(n, 1)}


def test_symmetry_alone_allows_the_third_element():
    bij = [tuple(p) for p in permutations(range(3))]
    sym = nt.natural_tables(3, bij)
    assert len(sym) == 3
    extra = [t for t in sym if t not in {nt.projection(3, 0), nt.projection(3, 1)}]
    assert len(extra) == 1 and nt.third_element(extra[0])
    # On two elements, four tables commute with the swap.
    assert len(nt.natural_tables(2, [(0, 1), (1, 0)])) == 4


def test_breaking_square_is_a_genuine_counterexample():
    t = tuple(a if a == b else 3 - a - b for a in range(3) for b in range(3))
    f, a, b, lhs, rhs = nt.breaking_square(t)
    assert lhs == t[f[a] * 3 + f[b]] and rhs == f[t[a * 3 + b]] and lhs != rhs
    assert len(set(f)) < 3, "the failing map is not injective"
    assert nt.breaking_square(nt.projection(3, 0)) is None
