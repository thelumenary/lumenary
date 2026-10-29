from fractions import Fraction

import functions_and_graphs_transformations as fgt


def cubic(x):
    return x ** 3 - x


def test_transform_matches_formula():
    g = fgt.transform(cubic, -1, 2, 1, 3)
    for x in [Fraction(0), Fraction(1, 2), Fraction(5, 3)]:
        assert g(x) == -cubic(2 * (x - 1)) + 3


def test_move_point_lands_on_new_graph():
    a, b, h, k = Fraction(-1), Fraction(2), Fraction(1), Fraction(3)
    assert fgt.move_point((Fraction(2), Fraction(6)), a, b, h, k) == (2, -3)
    assert fgt.rule_holds(cubic, a, b, h, k, fgt.GRID)
    assert fgt.rule_holds(lambda x: x * x, Fraction(3), Fraction(-1, 2), Fraction(-4), Fraction(1, 7), fgt.GRID)


def test_wrong_rule_is_detected():
    # Moving left instead of right (h -> -h) does not match y = f(x - h) in general.
    a, b, h, k = Fraction(1), Fraction(1), Fraction(2), Fraction(0)
    g = fgt.transform(cubic, a, b, h, k)
    wrong = [(x - h, cubic(x)) for x in fgt.GRID]
    assert any(g(u) != v for u, v in wrong)


def test_even_odd_parts_add_up_and_have_right_parity():
    f = lambda x: x ** 3 + 2 * x ** 2 - x + 5  # noqa: E731
    e, o = fgt.even_part(f), fgt.odd_part(f)
    for x in fgt.GRID:
        assert e(x) + o(x) == f(x)
    assert fgt.parity(e, fgt.GRID) == "even"
    assert fgt.parity(o, fgt.GRID) == "odd"
    assert e(Fraction(1)) == 7 and o(Fraction(1)) == 0


def test_parity_labels():
    assert fgt.parity(lambda x: x ** 2, fgt.GRID) == "even"
    assert fgt.parity(lambda x: x ** 3, fgt.GRID) == "odd"
    assert fgt.parity(lambda x: 0 * x, fgt.GRID) == "zero"
    assert fgt.parity(lambda x: x + 1, fgt.GRID) == "neither"
