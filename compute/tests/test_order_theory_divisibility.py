import math

import order_theory_divisibility as od


def test_hasse_diagram_of_one_to_twelve():
    edges = od.covers(list(range(1, 13)), od.divides)
    assert len(edges) == 14
    assert (2, 4) in edges and (4, 12) in edges and (6, 12) in edges
    assert (2, 12) not in edges and (1, 4) not in edges


def test_maximal_and_minimal():
    nums = list(range(1, 13))
    assert od.maximal(nums, od.divides) == [7, 8, 9, 10, 11, 12]
    assert od.maximal(nums, lambda a, b: od.divides(b, a)) == [1]


def test_lattices():
    assert od.lattice_check(list(range(1, 13)), od.divides) == (2, 7)
    d60 = [d for d in range(1, 61) if 60 % d == 0]
    assert od.lattice_check(d60, od.divides) is None
    for a in d60:
        for b in d60:
            assert od.least_upper_bound(d60, od.divides, a, b) == math.lcm(a, b)
    chain = list(range(5))
    assert od.lattice_check(chain, lambda a, b: a <= b) is None


def test_least_fixed_point_two_ways():
    fix, rounds = od.lfp_by_iteration(od.step)
    assert fix == frozenset({0, 1, 2, 3, 4}) and rounds == 4
    assert od.lfp_by_prefixed_points(od.step, range(8)) == fix
    assert od.step(fix) == fix
    # Starting elsewhere: 5 and 6 form a cycle reachable only from each other.
    f = lambda s: od.step(s, start=5)
    assert od.lfp_by_iteration(f)[0] == frozenset({5, 6})
    assert od.lfp_by_prefixed_points(f, range(8)) == frozenset({5, 6})
