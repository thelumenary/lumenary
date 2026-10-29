from fractions import Fraction

import research_ethics_agreement as a

HALF = Fraction(1, 2)
Q = Fraction(3, 5)


def test_single_checker_does_not_depend_on_correlation():
    for rho in [Fraction(0), Fraction(1, 3), HALF, Fraction(1)]:
        assert a.posterior(HALF, Q, rho, 1) == Fraction(5, 8)


def test_exact_values():
    assert a.accept_flawed(Q, 0, 2) == Fraction(9, 25)
    assert a.posterior(HALF, Q, 0, 2) == Fraction(25, 34)
    assert a.ceiling(HALF, Q, HALF) == Fraction(10, 13)
    # A checker that never accepts a flawed proof gives certainty.
    assert a.posterior(HALF, Fraction(0), 0, 1) == 1


def test_posterior_increases_but_stays_below_ceiling():
    for rho in [Fraction(1, 10), HALF, Fraction(9, 10)]:
        values = [a.posterior(HALF, Q, rho, k) for k in range(1, 40)]
        assert all(x < y for x, y in zip(values, values[1:]))
        assert all(v < a.ceiling(HALF, Q, rho) < 1 for v in values)


def test_independent_checkers_approach_certainty():
    assert a.posterior(HALF, Q, 0, 60) > 1 - Fraction(1, 10 ** 12)
    assert a.posterior(HALF, Q, 0, 60) < 1


def test_perfect_correlation_means_one_checker():
    for k in [1, 5, 50]:
        assert a.posterior(HALF, Q, 1, k) == a.posterior(HALF, Q, 0, 1)


def test_simulation_matches_formula_and_is_deterministic():
    est, n = a.simulate(0.5, 0.6, 0.5, 10, 40000)
    exact = float(a.posterior(HALF, Q, HALF, 10))
    assert abs(est - exact) < 4 * (exact * (1 - exact) / n) ** 0.5
    assert a.simulate(0.5, 0.6, 0.5, 10, 1000) == a.simulate(0.5, 0.6, 0.5, 10, 1000)
