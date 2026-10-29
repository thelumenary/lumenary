from fractions import Fraction

import algebraic_topology_lefschetz as al


def test_lefschetz_number_formula():
    assert al.lefschetz_number(((1, 0), (0, 1))) == 0
    assert al.lefschetz_number(((0, -1), (1, 0))) == 2
    assert al.lefschetz_number(((2, 1), (1, 1))) == -1
    assert al.lefschetz_number(((-1, 0), (0, -1))) == 4


def test_fixed_points_of_rotation_and_negation():
    assert al.fixed_points(((0, -1), (1, 0))) == [
        (Fraction(0), Fraction(0)), (Fraction(1, 2), Fraction(1, 2))]
    assert len(al.fixed_points(((-1, 0), (0, -1)))) == 4


def test_count_equals_abs_lefschetz_number():
    for a in al.MATRICES.values():
        pts = al.fixed_points(a)
        if pts is not None:
            assert len(pts) == abs(al.lefschetz_number(a))


def test_points_really_are_fixed():
    for a in al.MATRICES.values():
        for x, y in al.fixed_points(a) or []:
            fx = a[0][0] * x + a[0][1] * y
            fy = a[1][0] * x + a[1][1] * y
            assert (fx - x).denominator == 1 and (fy - y).denominator == 1


def test_degenerate_case_has_infinitely_many():
    assert al.fixed_points(((1, 1), (0, 1))) is None
    assert al.lefschetz_number(((1, 1), (0, 1))) == 0
