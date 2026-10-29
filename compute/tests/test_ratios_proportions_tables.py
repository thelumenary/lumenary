from fractions import Fraction

import ratios_proportions_tables as rt


def test_constant_of_proportionality():
    assert rt.constant_of_proportionality([(4, 6), (10, 15)]) == Fraction(3, 2)
    assert rt.constant_of_proportionality(
        rt.TABLES["euros to CFA francs"]) == Fraction(655957, 1000)
    assert rt.constant_of_proportionality([(1, 350), (2, 500)]) is None


def test_rows_through_zero():
    assert rt.constant_of_proportionality([(0, 0), (2, 6)]) == 3
    # A row (0, 5) is impossible for y = kx.
    assert rt.constant_of_proportionality([(0, 5), (2, 6)]) is None
    # Only the origin: no ratio to read off.
    assert rt.constant_of_proportionality([(0, 0)]) is None


def test_classification_of_lesson_tables():
    expected = {
        "millet flour (people, cups)": "proportional",
        "euros to CFA francs": "proportional",
        "taxi (km, fare)": "linear, not proportional",
        "square (side, perimeter)": "proportional",
        "square (side, area)": "not linear",
        "ages (Amara, brother)": "linear, not proportional",
    }
    assert {name: rt.classify(t) for name, t in rt.TABLES.items()} == expected


def test_is_linear_ignores_row_order():
    assert rt.is_linear([(5, 950), (1, 350), (2, 500)])
    assert not rt.is_linear([(3, 9), (1, 1), (2, 4)])


def test_adding_rows():
    flour = rt.TABLES["millet flour (people, cups)"]
    x, y = rt.add_rows(flour, 0, 1)
    assert (x, y) == (10, 15) and y == Fraction(3, 2) * x
    taxi = rt.TABLES["taxi (km, fare)"]
    x, y = rt.add_rows(taxi, 0, 1)
    assert (x, y) == (3, 850)
    assert rt.taxi_fare(3) == 650
    assert all(rt.taxi_fare(km) == fare for km, fare in taxi)
