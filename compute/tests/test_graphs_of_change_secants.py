from fractions import Fraction as F

import pytest

import graphs_of_change_secants as gs


def test_fallen_values():
    assert gs.fallen(0) == 0
    assert gs.fallen(1) == F(49, 10)
    assert gs.fallen(2) == F(98, 5)
    assert gs.fallen(F(1, 2)) == F(49, 40)


def test_average_speed_each_second_grows_by_9_8():
    speeds = [gs.avg_speed(t, t + 1) for t in range(6)]
    assert speeds[0] == F(49, 10)
    assert all(b - a == F(49, 5) for a, b in zip(speeds, speeds[1:]))


def test_formula_matches_for_many_h():
    for num in range(-50, 51):
        for den in (1, 3, 7, 10, 1000):
            h = F(num, den)
            if h != 0:
                assert gs.avg_speed(2, 2 + h) == gs.formula(h)


def test_averages_approach_19_6():
    errors = [abs(gs.avg_speed(2, 2 + F(1, 10 ** k)) - F(98, 5)) for k in range(1, 7)]
    assert all(b < a for a, b in zip(errors, errors[1:]))
    assert errors[-1] == F(49, 10) / 10 ** 6


def test_guard_and_show():
    with pytest.raises(ValueError):
        gs.avg_speed(2, 2)
    assert gs.show(F(40)) == "40"
    assert gs.show(F(2009, 100)) == "2009/100 (= 20.0900)"
