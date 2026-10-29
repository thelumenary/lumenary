import random
from fractions import Fraction as F

import monads_kleisli_kernels as mk


def test_unit_and_flatten():
    assert mk.unit("a") == {"a": F(1)}
    mixed = mk.flatten([(F(1, 2), {0: F(1)}), (F(1, 2), {0: F(1, 2), 1: F(1, 2)})])
    assert mixed == {0: F(3, 4), 1: F(1, 4)}
    # Zero-probability outcomes are dropped.
    assert mk.flatten([(F(1), {0: F(1)}), (F(0), {1: F(1)})]) == {0: F(1)}


def test_kleisli_is_matrix_product_on_an_example():
    a = [[F(1, 2), F(1, 2)], [F(0), F(1)]]
    b = [[F(1, 3), F(2, 3)], [F(1), F(0)]]
    comp = mk.kleisli(mk.kernel_from_matrix(a), mk.kernel_from_matrix(b))
    assert mk.matrix_from_kernel(comp, 2, 2) == mk.mat_mul(a, b)
    assert mk.mat_mul(a, b) == [[F(2, 3), F(1, 3)], [F(1), F(0)]]


def test_dirac_is_kleisli_identity():
    m = [[F(1, 4), F(3, 4)], [F(1, 2), F(1, 2)], [F(1), F(0)]]
    k = mk.kernel_from_matrix(m)
    assert mk.matrix_from_kernel(mk.kleisli(mk.unit, k), 3, 2) == m
    assert mk.matrix_from_kernel(mk.kleisli(k, mk.unit), 3, 2) == m


def test_random_stochastic_rows_sum_to_one():
    rng = random.Random(7)
    for _ in range(50):
        m = mk.random_stochastic(3, 4, rng)
        assert all(sum(row) == 1 and min(row) >= 0 for row in m)


def test_expectation_and_tower_property():
    assert mk.expectation({F(2): F(1, 2), F(4): F(1, 2)}) == 3
    mixture = [(F(1, 3), {F(0): F(1)}), (F(2, 3), {F(3): F(1, 2), F(9): F(1, 2)})]
    assert mk.tower_property_holds(mixture)
    assert mk.expectation(mk.flatten(mixture)) == 4


def test_no_failures_in_trials():
    fails = mk.run_trials(60, random.Random(1))
    assert fails == {"matrix": 0, "assoc": 0, "unit": 0, "tower": 0}


def test_a_non_algebra_map_breaks_the_associativity_law():
    # Averaging the support while ignoring the probabilities obeys the unit
    # law but is not an algebra for D.
    def support_mean(dist):
        return sum(dist, F(0)) / len(dist)

    d1 = {F(0): F(1)}
    d2 = {F(0): F(1, 2), F(2): F(1, 2)}
    mixture = [(F(1, 2), d1), (F(1, 2), d2)]
    assert support_mean({F(5): F(1)}) == 5
    outer = {support_mean(d1): F(1, 2), support_mean(d2): F(1, 2)}
    assert support_mean(outer) == F(1, 2)
    assert support_mean(mk.flatten(mixture)) == 1
