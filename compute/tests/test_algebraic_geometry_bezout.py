import pytest

import algebraic_geometry_bezout as ab

X, Y, Z = ab.X, ab.Y, ab.Z


def test_degrees():
    assert ab.degree(ab.CIRCLE) == 2
    assert ab.degree(Y**2 * Z - X**3) == 3
    assert ab.degree(Z) == 1


@pytest.mark.parametrize("change", ab.CHANGES)
def test_every_example_gives_d_times_e(change):
    for _, f, g in ab.EXAMPLES:
        pattern = ab.intersection_pattern(f, g, change)
        assert ab.total(pattern) == ab.degree(f) * ab.degree(g)


def test_tangency_and_points_at_infinity():
    tangent = ab.intersection_pattern(ab.CIRCLE, Y - Z, ab.CHANGES[0])
    assert tangent == [(1, 2)]                       # one double point
    cusp = ab.intersection_pattern(Y**2 * Z - X**3, Y, ab.CHANGES[1])
    assert cusp == [(1, 3)]                          # the cuspidal tangent
    concentric = ab.intersection_pattern(ab.CIRCLE, X**2 + Y**2 - 4 * Z**2,
                                         ab.CHANGES[0])
    assert concentric == [(2, 2)]                    # [1:i:0], [1:-i:0] twice


def test_patterns_independent_of_coordinates():
    for _, f, g in ab.EXAMPLES:
        first, second = (ab.intersection_pattern(f, g, c) for c in ab.CHANGES)
        assert first == second


def test_non_generic_and_common_component_rejected():
    with pytest.raises(ValueError):
        ab.intersection_pattern(ab.CIRCLE, X, {X: X, Y: Y, Z: Z})  # [0:0:1] on x = 0
    with pytest.raises(ValueError):
        ab.intersection_pattern(X * Y, X * (X + Y + Z), ab.CHANGES[0])


def test_describe_and_total():
    assert ab.describe([(1, 1), (1, 2)]) == "1 pt x2 + 1 pt x1"
    assert ab.total([(2, 1), (2, 1)]) == 4
    assert ab.is_generic(ab.CIRCLE, Y - 2 * Z)
    assert not ab.is_generic(ab.CIRCLE, X)
