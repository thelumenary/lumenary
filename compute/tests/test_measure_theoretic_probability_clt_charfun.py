import math

import pytest

import measure_theoretic_probability_clt_charfun as cf


def test_charfun_basic_values():
    assert cf.charfun_sum(0.0, 7) == 1.0
    assert cf.charfun_sum(1.0, 1) == pytest.approx(math.cos(1.0))
    with pytest.raises(ValueError):
        cf.charfun_sum(1.0, 0)


def test_charfun_converges_to_gaussian_at_rate_one_over_n():
    for t in [0.5, 1.0, 2.0, 3.0]:
        err = abs(cf.charfun_sum(t, 10 ** 5) - math.exp(-t * t / 2))
        assert err < 1e-4
    e1, e2 = cf.max_charfun_error(1000), cf.max_charfun_error(10000)
    assert e2 < e1
    assert 1000 * e1 == pytest.approx(16 / (12 * math.e ** 2), rel=0.01)


def test_normal_cdf():
    assert cf.normal_cdf(0) == pytest.approx(0.5)
    assert cf.normal_cdf(1.96) == pytest.approx(0.975, abs=1e-3)
    assert cf.normal_cdf(-1) == pytest.approx(1 - cf.normal_cdf(1))


def test_binomial_cdf_error_berry_esseen_scale():
    e100, e1000 = cf.binomial_cdf_error(100), cf.binomial_cdf_error(1000)
    assert e1000 < e100
    assert math.sqrt(1000) * e1000 == pytest.approx(1 / math.sqrt(2 * math.pi), rel=0.01)
    # for n = 1 the law is +-1 with probability 1/2 each
    assert cf.binomial_cdf_error(1) == pytest.approx(cf.normal_cdf(1) - 0.5)
