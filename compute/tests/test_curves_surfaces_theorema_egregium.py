import math

import pytest
import sympy

import curves_surfaces_theorema_egregium as te

U, V, R = te.U, te.V, te.R


def test_sphere_forms_and_curvature():
    X = te.surfaces()["sphere (radius R)"]
    E, F, G = te.first_form(X)
    assert sympy.simplify(E - R**2 * sympy.cos(V) ** 2) == 0
    assert F == 0 and sympy.simplify(G - R**2) == 0
    assert sympy.simplify(te.brioschi(E, F, G) - 1 / R**2) == 0
    assert sympy.simplify(te.extrinsic_curvature(X) - 1 / R**2) == 0


def test_brioschi_matches_extrinsic_on_all_examples():
    for X in te.surfaces().values():
        E, F, G = te.first_form(X)
        assert sympy.simplify(te.extrinsic_curvature(X) - te.brioschi(E, F, G)) == 0


def test_catenoid_and_helicoid_are_locally_isometric():
    s = te.surfaces()
    assert te.first_form(s["catenoid"]) == te.first_form(s["helicoid"])
    k = sympy.simplify(te.extrinsic_curvature(s["helicoid"]))
    assert sympy.simplify(k + 1 / sympy.cosh(U) ** 4) == 0


def test_flat_and_saddle_signs():
    s = te.surfaces()
    assert sympy.simplify(te.extrinsic_curvature(s["cylinder"])) == 0
    k = te.extrinsic_curvature(s["saddle z = uv"]).subs({U: 0, V: 0})
    assert sympy.simplify(k) == -1


def test_ellipsoid_gauss_bonnet():
    assert te.ellipsoid_total_curvature(1.0, 1.0, 1.0, n=80) == pytest.approx(4 * math.pi, rel=1e-3)
    assert te.ellipsoid_total_curvature(3.0, 1.0, 0.5, n=150) == pytest.approx(4 * math.pi, rel=1e-3)
