import math
from fractions import Fraction

import computational_reproducibility_floating_point as fp


def test_exact_sum_matches_fractions():
    xs = [0.1, 0.2, 0.3, -1e-300, 1e300, -1e300]
    assert fp.exact_sum(xs) == sum(Fraction(x) for x in xs)
    assert fp.exact_sum([]) == 0


def test_addition_is_not_associative():
    assert (0.1 + 0.2) + 0.3 != 0.1 + (0.2 + 0.3)
    assert Fraction(0.1) != Fraction(1, 10)


def test_fsum_is_the_correctly_rounded_exact_sum():
    xs = fp.make_data(5000, seed=3)
    assert math.fsum(xs) == float(fp.exact_sum(xs))


def test_recursive_errors_respect_the_proven_bound():
    xs = fp.make_data(20000, seed=11)
    exact = fp.exact_sum(xs)
    bound = fp.recursive_bound(xs)
    for order in (xs, sorted(xs), sorted(xs, key=abs, reverse=True)):
        assert abs(Fraction(fp.recursive_sum(order)) - exact) <= Fraction(bound)


def test_compensated_and_pairwise_beat_plain_summation_on_the_lesson_data():
    xs = fp.make_data(100_000)
    exact = fp.exact_sum(xs)
    err = lambda v: abs(Fraction(v) - exact)
    plain = err(fp.recursive_sum(xs))
    assert err(fp.kahan_sum(xs)) < plain
    assert err(fp.pairwise_sum(xs)) < plain


def test_kahan_error_bound():
    # Kahan: |error| <= (2u + O(n u^2)) * sum |x_i|; check with a generous constant
    for seed in range(5):
        xs = fp.make_data(10_000, seed=seed)
        exact = fp.exact_sum(xs)
        total = math.fsum(abs(x) for x in xs)
        bound = (2 * fp.U + 4 * len(xs) * fp.U ** 2) * total
        assert abs(Fraction(fp.kahan_sum(xs)) - exact) <= Fraction(bound)


def test_small_cases_and_determinism():
    assert fp.pairwise_sum([1.0, 2.0, 3.0]) == 6.0
    assert fp.kahan_sum([]) == 0.0
    assert fp.make_data(10) == fp.make_data(10)
    assert fp.make_data(10, seed=1) != fp.make_data(10, seed=2)
    assert fp.recursive_bound([1.0]) == 0.0
