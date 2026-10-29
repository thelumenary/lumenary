from fractions import Fraction

import statistics_intro_best_centre as sb


def test_grid():
    g = sb.grid(0, 1, Fraction(1, 4))
    assert g == [0, Fraction(1, 4), Fraction(1, 2), Fraction(3, 4), 1]
    assert len(sb.grid(0, 50, Fraction(1, 4))) == 201


def test_costs_small_example():
    data = [1, 2, 6]
    assert sb.total_distance(data, 2) == 1 + 0 + 4
    assert sb.total_squared_distance(data, 3) == 4 + 1 + 9


def test_median_minimises_total_distance():
    cands = sb.grid(0, 50, Fraction(1, 4))
    assert sb.minimisers(sb.DATA, sb.total_distance, cands) == [15]


def test_mean_minimises_total_squared_distance_exactly():
    m = Fraction(sum(sb.DATA), len(sb.DATA))
    cands = sb.grid(0, 50, Fraction(1, 4)) + [m]
    assert sb.minimisers(sb.DATA, sb.total_squared_distance, cands) == [m]


def test_identity_on_grid_and_other_data():
    assert sb.identity_holds(sb.DATA, sb.grid(0, 50, Fraction(1, 4)))
    assert sb.identity_holds([3, -1, Fraction(7, 2)], sb.grid(-5, 5, Fraction(1, 3)))


def test_even_count_has_flat_minimum():
    flat = sb.minimisers([1, 2, 6, 10], sb.total_distance, sb.grid(0, 12, Fraction(1, 2)))
    assert flat[0] == 2 and flat[-1] == 6 and len(flat) == 9
