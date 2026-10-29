from fractions import Fraction as F

import pytest

import linear_relationships_systems as lr


def test_slope_exact_and_vertical():
    assert lr.slope((0, 32), (100, 212)) == F(9, 5)
    assert lr.slope((3, 1), (1, 5)) == -2
    assert lr.slope((1, 5), (3, 1)) == lr.slope((3, 1), (1, 5))
    with pytest.raises(ValueError):
        lr.slope((2, 0), (2, 7))


def test_linear_fit_tables():
    assert lr.linear_fit(lr.TABLES["taxi fare (km, soles)"]) == (2, 5)
    assert lr.linear_fit(lr.TABLES["Celsius -> Fahrenheit"]) == (F(9, 5), 32)
    assert lr.linear_fit(lr.TABLES["rice, kg -> rupees"]) == (60, 0)
    assert lr.linear_fit(lr.TABLES["square: side -> area"]) is None


def test_line_text():
    assert lr.line_text(F(2), F(5)) == "y = 2x + 5"
    assert lr.line_text(F(9, 5), F(32)) == "y = (9/5)x + 32"
    assert lr.line_text(F(60), F(0)) == "y = 60x"
    assert lr.line_text(F(-1), F(-3)) == "y = -1x - 3"


def test_classify_lesson_systems():
    assert lr.classify(*lr.SYSTEMS["chickens and rabbits"]) == ("one", (23, 12))
    assert lr.classify(*lr.SYSTEMS["y = 1.8x + 32, y = x"]) == ("one", (-40, -40))
    assert lr.classify(*lr.SYSTEMS["x + y = 3, 2x + 2y = 10"]) == ("none", None)
    assert lr.classify(*lr.SYSTEMS["x + 2y = 4, 2x + 4y = 8"]) == ("infinite", None)


def test_classify_degenerate_rows():
    # 0x + 0y = 0 together with a genuine line: a whole line of solutions
    assert lr.classify(0, 0, 0, 1, 1, 2) == ("infinite", None)
    # 0x + 0y = 3 is never true
    assert lr.classify(0, 0, 3, 1, 1, 2) == ("none", None)
    assert lr.classify(0, 0, 0, 0, 0, 0) == ("infinite", None)
    assert lr.classify(0, 0, 0, 0, 0, 1) == ("none", None)


def test_census_is_complete_and_unique_solutions_check():
    counts, bad = lr.census(range(-1, 2))
    assert sum(counts.values()) == 3 ** 6
    assert bad == 0
    counts, bad = lr.census(range(-2, 3))
    assert sum(counts.values()) == 5 ** 6 and bad == 0
    # a system has a unique solution exactly when its determinant is non-zero:
    nonsingular = sum(1 for a in range(-2, 3) for b in range(-2, 3)
                      for c in range(-2, 3) for d in range(-2, 3) if a * d - b * c != 0)
    assert counts["one"] == nonsingular * 25
