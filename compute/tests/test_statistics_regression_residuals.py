from fractions import Fraction

import pytest

import statistics_regression_residuals as ex


def test_exact_line_through_collinear_points():
    b0, b1 = ex.normal_equations_line([0, 1, 2], [1, 3, 5])
    assert (b0, b1) == (1, 2)
    with pytest.raises(ValueError):
        ex.normal_equations_line([2, 2], [1, 3])


def test_residuals_orthogonal_to_columns():
    b0, b1 = ex.normal_equations_line(ex.MASS, ex.EXTENSION)
    res = ex.residuals(ex.MASS, ex.EXTENSION, b0, b1)
    assert sum(res) == 0
    assert sum(Fraction(x) * e for x, e in zip(ex.MASS, res)) == 0
    assert (b0, b1) == (Fraction(8, 105), Fraction(347, 175))


def test_numpy_agrees_with_exact_fit():
    b0, b1 = ex.normal_equations_line(ex.MASS, ex.EXTENSION)
    _, _, nb1, nb0, _, _ = ex.summary(ex.MASS, [float(e) for e in ex.EXTENSION])
    assert nb0 == pytest.approx(float(b0)) and nb1 == pytest.approx(float(b1))


@pytest.mark.parametrize("name", ["I", "II", "III", "IV"])
def test_anscombe_summaries_agree(name):
    mx, my, slope, intercept, r, _ = ex.summary(*ex.ANSCOMBE[name])
    assert mx == pytest.approx(9.0)
    assert my == pytest.approx(7.50, abs=0.01)
    assert slope == pytest.approx(0.500, abs=0.002)
    assert intercept == pytest.approx(3.00, abs=0.01)
    assert r == pytest.approx(0.816, abs=0.002)


def test_anscombe_diagnostics_differ():
    assert ex.curvature(*ex.ANSCOMBE["II"]) < -0.95
    big, i, _ = ex.diagnostics(*ex.ANSCOMBE["III"])
    assert big > 3 and ex.ANSCOMBE["III"][1][i] == 12.74
    _, _, lev = ex.diagnostics(*ex.ANSCOMBE["IV"])
    assert lev == pytest.approx(1.0)
    assert ex.curvature(*ex.ANSCOMBE["IV"]) == pytest.approx(0.0, abs=1e-9)
