import math
from fractions import Fraction

import geometric_group_theory_random_walks as rw


def test_small_return_probabilities():
    assert rw.z2_return(1) == Fraction(1, 4)
    assert rw.z2_return(2) == Fraction(36, 256)
    assert rw.tree_return(1) == Fraction(1, 4)
    # Two steps out and two back, or out-back-out-back: 1/4 * 3/4 * 1/4 + 1/16.
    assert rw.tree_return(2) == Fraction(3, 64) + Fraction(1, 16)


def test_z2_formula_matches_counting():
    for n in range(6):
        assert rw.z2_return(n) == rw.z2_return_by_counting(n)


def test_tree_on_degree_two_is_the_integers():
    # The 2-regular tree is Z: p(2n) = C(2n, n) / 4^n.
    for n in range(8):
        assert rw.tree_return(n, degree=2) == Fraction(math.comb(2 * n, n), 4 ** n)


def test_tree_returns_exponentially_less_often():
    for n in (5, 10, 20):
        assert rw.tree_return(n) < rw.z2_return(n)
    assert rw.nth_root(rw.tree_return(80), 80) < math.sqrt(3) / 2


def test_even_return_probabilities_decrease():
    # For a symmetric random walk on a group, p(2n + 2) <= p(2n).
    tree = [rw.tree_return(n) for n in range(30)]
    z2 = [rw.z2_return(n) for n in range(30)]
    assert all(a > b for a, b in zip(tree, tree[1:]))
    assert all(a > b for a, b in zip(z2, z2[1:]))


def test_nth_root():
    assert abs(rw.nth_root(Fraction(1, 4), 1) - 0.5) < 1e-12
