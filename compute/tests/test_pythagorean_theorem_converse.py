import math
from fractions import Fraction

import pythagorean_theorem_converse as pc


def test_triangle_list():
    tris = pc.triangles(20)
    assert len(tris) == 825
    assert (1, 1, 1) in tris and (3, 4, 5) in tris
    assert (1, 2, 3) not in tris  # degenerate: 1 + 2 = 3


def test_apex_is_exact_and_correct():
    x, y = pc.apex(3, 4, 5)
    assert x == 0 and math.isclose(y, 4)
    x, y = pc.apex(5, 6, 8)
    assert x == Fraction(-3, 10)
    # A really is at distance b from C and c from B.
    for a, b, c in [(5, 6, 8), (4, 5, 6), (7, 7, 7)]:
        x, y = pc.apex(a, b, c)
        assert math.isclose(math.hypot(float(x), y), b)
        assert math.isclose(math.hypot(float(x) - a, y), c)


def test_pythagoras_test_classification():
    assert pc.pythagoras_test(3, 4, 5) == "right"
    assert pc.pythagoras_test(5, 6, 8) == "obtuse"
    assert pc.pythagoras_test(4, 5, 6) == "acute"
    assert pc.pythagoras_test(1, 1, 1) == "acute"


def test_measurement_agrees_everywhere():
    for t in pc.triangles(20):
        assert pc.measured_type(*t) == pc.pythagoras_test(*t)


def test_angles():
    assert math.isclose(pc.angle_at_c(3, 4, 5), 90)
    assert math.isclose(pc.angle_at_c(1, 1, 1), 60)
    assert pc.angle_at_c(5, 6, 8) > 90
