import random
from fractions import Fraction

import statistical_inference_intro_regression as sr


def test_sums_on_a_perfect_line():
    x = [1, 2, 3, 4]
    y = [Fraction(3 + 2 * v) for v in x]
    mx, my, sxx, sxy, syy = sr.sums(x, y)
    assert (mx, my, sxx, sxy, syy) == (Fraction(5, 2), 8, 5, 10, 20)
    assert sr.least_squares(x, y) == (3, 2)
    assert abs(sr.correlation(x, y) - 1) < 1e-12
    assert abs(sr.correlation(x, [-v for v in y]) + 1) < 1e-12


def test_anscombe_summaries_agree():
    lines, rs = [], []
    for x, ys in sr.ANSCOMBE.values():
        y = [Fraction(v) for v in ys]
        a, b = sr.least_squares(x, y)
        lines.append((round(float(a), 2), round(float(b), 3)))
        rs.append(sr.correlation(x, y))
        assert sr.sums(x, y)[0] == 9
    assert set(lines) == {(3.0, 0.5)}
    assert all(abs(r - 0.816) < 0.002 for r in rs)


def test_residuals_sum_to_zero_and_line_passes_through_means():
    x, ys = sr.ANSCOMBE["III"]
    y = [Fraction(v) for v in ys]
    assert sum(sr.residuals(x, y)) == 0
    a, b = sr.least_squares(x, y)
    mx, my = sr.sums(x, y)[:2]
    assert a + b * mx == my


def test_parabola_has_zero_correlation():
    xs = list(range(-3, 4))
    assert sr.sums(xs, [v * v for v in xs])[3] == 0
    assert sr.correlation(xs, [v * v for v in xs]) == 0


def test_confounding_disappears_after_adjustment():
    temp, ice, rescues = sr.confounded_town(random.Random(5), 3000)
    assert sr.correlation(ice, rescues) > 0.5
    left = sr.correlation(sr.residuals(temp, ice), sr.residuals(temp, rescues))
    assert abs(left) < 0.1
