import sympy

import riemannian_geometry_curvature as rc

U, V = rc.U, rc.V


def test_model_curvatures():
    sphere = sympy.Matrix([[1, 0], [0, sympy.sin(U) ** 2]])
    plane = sympy.Matrix([[1, 0], [0, 1]])
    half_plane = sympy.Matrix([[1 / V**2, 0], [0, 1 / V**2]])
    assert rc.gaussian_curvature(sphere) == 1
    assert rc.gaussian_curvature(plane) == 0
    assert rc.gaussian_curvature(half_plane) == -1


def test_scaling_a_metric_scales_curvature():
    # The sphere of radius 3 has metric 9(du^2 + sin^2 u dv^2) and K = 1/9.
    sphere3 = sympy.Matrix([[9, 0], [0, 9 * sympy.sin(U) ** 2]])
    assert rc.gaussian_curvature(sphere3) == sympy.Rational(1, 9)


def test_surface_of_revolution_formula():
    # dt^2 + f(t)^2 dtheta^2 has K = -f''/f; try f = cosh (a catenoid-like profile).
    f = sympy.cosh(U)
    g = sympy.Matrix([[1, 0], [0, f**2]])
    expr = rc.gaussian_curvature(g) + sympy.diff(f, U, 2) / f
    for u in [0.1, 0.7, 1.9]:
        assert abs(float(expr.subs(U, u))) < 1e-12


def test_half_plane_christoffel():
    gam = rc.christoffel(sympy.Matrix([[1 / V**2, 0], [0, 1 / V**2]]))
    assert gam[0][0][1] == -1 / V
    assert gam[1][0][0] == 1 / V
    assert gam[1][1][1] == -1 / V
    assert gam[0][0][0] == 0 and gam[1][0][1] == 0


def test_gauss_bonnet_sphere_and_torus():
    sphere = sympy.Matrix([[1, 0], [0, sympy.sin(U) ** 2]])
    assert rc.integral_of_curvature(sphere, (0, sympy.pi), (0, 2 * sympy.pi)) == 4 * sympy.pi
    torus = sympy.Matrix([[(3 + sympy.cos(V)) ** 2, 0], [0, 1]])
    assert rc.integral_of_curvature(torus, (0, 2 * sympy.pi), (0, 2 * sympy.pi)) == 0
