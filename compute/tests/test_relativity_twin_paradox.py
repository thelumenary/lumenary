from fractions import Fraction

import pytest

import relativity_twin_paradox as tp


def test_rational_gamma_factors():
    assert tp.gamma_rational(Fraction(3, 5)) == Fraction(5, 4)
    assert tp.gamma_rational(Fraction(12, 13)) == Fraction(13, 5)
    assert tp.gamma_rational(0) == 1
    assert tp.gamma_rational(Fraction(1, 2)) is None  # 1/sqrt(3/4) is irrational
    with pytest.raises(ValueError):
        tp.gamma_rational(1)


def test_interval_and_reverse_triangle():
    assert tp.interval_sq(5, [3, 0, 0]) == 16
    assert tp.reverse_triangle_holds((Fraction(5), [Fraction(3)]), (Fraction(5), [Fraction(-3)]))
    # twins: two legs of proper time 4 each, straight path proper time 10
    assert tp.interval_sq(10, [0]) == 100
    # parallel vectors give equality: tau = 4 + 8 = 12 = tau of the sum
    v, w = (Fraction(5), [Fraction(3)]), (Fraction(10), [Fraction(6)])
    assert tp.interval_sq(15, [9]) == 144
    assert tp.reverse_triangle_holds(v, w)


def test_velocity_addition_identities():
    for u, v in [(Fraction(3, 5), Fraction(3, 5)), (Fraction(4, 5), Fraction(5, 13))]:
        w = tp.add_velocities(u, v)
        assert abs(w) < 1
        assert tp.gamma_rational(w) == tp.gamma_rational(u) * tp.gamma_rational(v) * (1 + u * v)
    assert tp.add_velocities(Fraction(1, 2), Fraction(-1, 2)) == 0


def test_random_vectors_are_future_timelike_and_satisfy_inequality():
    import random
    rng = random.Random(0)
    for _ in range(300):
        v, w = tp.random_future_timelike(rng), tp.random_future_timelike(rng)
        assert tp.interval_sq(*v) > 0 and v[0] > 0
        assert tp.reverse_triangle_holds(v, w)
