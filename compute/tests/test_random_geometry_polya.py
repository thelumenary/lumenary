import math
from fractions import Fraction

import pytest

import random_geometry_polya as rp


def test_closed_walks_match_rotation_trick():
    for n in range(1, 4):
        assert rp.closed_walks_2d(n) == math.comb(2 * n, n) ** 2


def test_u1_matches_binomial_formula():
    u = rp.u1(30)
    for n in [0, 1, 5, 17, 30]:
        assert u[n] == pytest.approx(math.comb(2 * n, n) / 4 ** n, rel=1e-12)


def test_u3_small_values_exact():
    # P(S_2 = 0) = 1/6; P(S_4 = 0) = 90/1296 = 5/72 for simple random walk on Z^3
    u = rp.u3(3)
    assert u[0] == pytest.approx(1.0)
    assert u[1] == pytest.approx(1 / 6, rel=1e-12)
    exact2 = Fraction(0)
    for i in range(3):
        for j in range(3 - i):
            k = 2 - i - j
            exact2 += Fraction(math.factorial(4),
                               (math.factorial(i) * math.factorial(j) * math.factorial(k)) ** 2)
    exact2 /= 6 ** 4
    assert exact2 == Fraction(5, 72)
    assert u[2] == pytest.approx(float(exact2), rel=1e-12)


def test_u3_against_multinomial_formula():
    u = rp.u3(12)
    for n in [5, 12]:
        s = Fraction(0)
        for i in range(n + 1):
            for j in range(n + 1 - i):
                k = n - i - j
                s += Fraction(math.factorial(2 * n),
                              (math.factorial(i) * math.factorial(j) * math.factorial(k)) ** 2)
        assert u[n] == pytest.approx(float(s / 6 ** (2 * n)), rel=1e-10)


def test_partial_sums_and_growth():
    one = rp.u1(10000)
    g1 = rp.partial_sums(one, {10000})
    assert g1[10000] == pytest.approx(2 * math.sqrt(10000 / math.pi), rel=0.01)
    g2 = rp.partial_sums([x * x for x in one], {100, 10000})
    # increments of the 2D Green function match log(N)/pi
    assert g2[10000] - g2[100] == pytest.approx(math.log(100) / math.pi, rel=0.01)


def test_watson_constant_and_3d_convergence():
    w = rp.watson_constant()
    assert w == pytest.approx(1.516386059, rel=1e-8)
    assert 1 - 1 / w == pytest.approx(0.340537, abs=1e-6)
    g3 = rp.partial_sums(rp.u3(400), {400})[400]
    assert g3 < w
    assert w - g3 < 0.03
