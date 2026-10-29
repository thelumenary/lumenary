import sympy

import multivariable_calculus_lagrange as lg

x, y, z = lg.x, lg.y, lg.z


def test_xy_on_circle():
    pts = lg.lagrange_points(x * y, x**2 + y**2, 2, (x, y))
    assert {p for p, _ in pts} == {(1, 1), (-1, -1), (1, -1), (-1, 1)}
    values = sorted(v for _, v in pts)
    assert values == [-1, -1, 1, 1]


def test_box_of_given_surface_area_is_a_cube():
    pts = lg.lagrange_points(x * y * z, 2 * (x * y + y * z + z * x), 6, (x, y, z))
    positive = [(p, v) for p, v in pts if all(t > 0 for t in p)]
    assert positive == [((1, 1, 1), 1)]


def test_nearest_point_of_plane():
    pts = lg.lagrange_points(x**2 + y**2 + z**2, x + 2 * y + 2 * z, 9, (x, y, z))
    assert pts == [((1, 2, 2), 9)]
    # The distance is |9| / |(1, 2, 2)| = 3.
    assert sympy.sqrt(pts[0][1]) == 3


def test_multiplier_rule_check():
    f, g = x * y, x**2 + y**2
    assert lg.satisfies_multiplier_rule(f, g, (1, 1), (x, y))
    assert not lg.satisfies_multiplier_rule(f, g, (sympy.sqrt(2), 0), (x, y))


def test_every_listed_point_satisfies_the_constraint():
    for _, f, g, c, variables in lg.PROBLEMS:
        for point, _ in lg.lagrange_points(f, g, c, variables):
            assert sympy.simplify(g.subs(dict(zip(variables, point))) - c) == 0
