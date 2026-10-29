from fractions import Fraction

import proof_techniques_circle_regions as cr


def test_circle_points_are_on_the_unit_circle():
    for t in cr.PARAMS + [Fraction(-3, 4), Fraction(100)]:
        x, y = cr.circle_point(t)
        assert isinstance(x, Fraction) and isinstance(y, Fraction)
        assert x * x + y * y == 1
    for x, y in cr.HEXAGON_WITH_DIAMETERS:
        assert x * x + y * y == 1


def test_crossing_of_diameters_is_the_centre():
    a, b, c, d = cr.HEXAGON_WITH_DIAMETERS[:4]
    assert cr.crossing(a, b, c, d) == (0, 0)
    # Chords with a common endpoint, or non-crossing chords, give None.
    p = [cr.circle_point(t) for t in cr.PARAMS[:4]]
    assert cr.crossing(p[0], p[1], p[2], p[3]) is None


def test_region_counts_match_general_position_formula():
    expected = [1, 2, 4, 8, 16, 31, 57, 99]
    for n in range(1, 9):
        pts = [cr.circle_point(t) for t in cr.PARAMS[:n]]
        assert cr.regions(pts) == expected[n - 1] == cr.general_position_formula(n)


def test_pattern_breaks_at_six():
    pts = [cr.circle_point(t) for t in cr.PARAMS[:6]]
    assert cr.regions(pts) == 31 != 2 ** 5


def test_concurrent_diameters_lose_a_region():
    assert cr.regions(cr.HEXAGON_WITH_DIAMETERS) == 30


def test_four_points_any_order_give_eight():
    pts = [cr.circle_point(t) for t in (Fraction(5), Fraction(-1, 3), Fraction(1, 2), Fraction(0))]
    assert cr.regions(pts) == 8
