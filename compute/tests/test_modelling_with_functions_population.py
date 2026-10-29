import math

import pytest

import modelling_with_functions_population as mp


def test_fit_line_exact_on_collinear_points():
    m, c = mp.fit_line([0, 1, 2, 3], [1, 3, 5, 7])
    assert math.isclose(m, 2) and math.isclose(c, 1)
    with pytest.raises(ValueError):
        mp.fit_line([1, 1], [2, 3])


def test_fit_exponential_recovers_parameters():
    ts = [0, 5, 10, 15]
    ps = [3.0 * math.exp(0.02 * t) for t in ts]
    a, r = mp.fit_exponential(ts, ps)
    assert math.isclose(a, 3.0) and math.isclose(r, 0.02)


def test_doubling_time():
    assert math.isclose(mp.doubling_time(math.log(2) / 10), 10)
    assert round(mp.doubling_time(0.0191)) == 36
    with pytest.raises(ValueError):
        mp.doubling_time(0)


def test_data_and_forecast_behaviour():
    assert len(mp.YEARS) == len(mp.POPULATION) == 8
    ts = [y - 1950 for y in mp.YEARS]
    m, c = mp.fit_line(ts[:4], mp.POPULATION[:4])
    a, r = mp.fit_exponential(ts[:4], mp.POPULATION[:4])
    # both fit the training decades closely ...
    for t, p in zip(ts[:4], mp.POPULATION[:4]):
        assert abs(c + m * t - p) < 0.1 and abs(a * math.exp(r * t) - p) < 0.1
    # ... but in 2020 the exponential overshoots and the line undershoots
    assert a * math.exp(r * 70) - mp.POPULATION[-1] > 1.0
    assert c + m * 70 - mp.POPULATION[-1] < -0.5
