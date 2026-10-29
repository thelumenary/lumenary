from fractions import Fraction as F

import pytest

import graphs_of_change_journey as gj


def test_avg_rate_exact_and_guarded():
    assert gj.avg_rate((0, 0), (20, 4)) == F(1, 5)
    assert gj.avg_rate((55, 6), (75, 0)) == F(-3, 10)
    assert gj.avg_rate((20, 4), (0, 0)) == gj.avg_rate((0, 0), (20, 4))
    with pytest.raises(ValueError):
        gj.avg_rate((5, 1), (5, 2))


def test_segments_and_descriptions():
    rates = [r for _, _, r in gj.segment_rates(gj.JOURNEY)]
    assert [60 * r for r in rates] == [12, 0, 12, 0, -18]
    assert gj.describe(F(1)).startswith("increasing")
    assert gj.describe(F(0)).startswith("constant")
    assert gj.describe(F(-1, 2)).startswith("decreasing")


def test_weighted_average_rule_everywhere():
    n = len(gj.JOURNEY)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                assert gj.weighted_average_holds(gj.JOURNEY, i, j, k)
    # also for a table that is not piecewise linear in any nice way
    table = [(0, 3), (1, 7), (4, -2), (9, 11)]
    assert gj.weighted_average_holds(table, 0, 2, 3)


def test_round_trip_zero_net_change_but_positive_speed():
    assert gj.avg_rate(gj.JOURNEY[0], gj.JOURNEY[-1]) == 0
    assert gj.distance_ridden(gj.JOURNEY) == 12


def test_round_trip_speed_is_harmonic_mean_and_at_most_mean():
    assert gj.round_trip_speed(30, 60) == 40
    assert gj.round_trip_speed(40, 40) == 40
    for u in range(1, 30):
        for v in range(1, 30):
            avg = gj.round_trip_speed(u, v)
            assert avg <= F(u + v, 2)
            assert (avg == F(u + v, 2)) == (u == v)
            assert min(u, v) <= avg <= max(u, v)
    with pytest.raises(ValueError):
        gj.round_trip_speed(0, 5)
