import sympy as sp

import relativity_schwarzschild_curvature as sc


def test_metric_shape_and_flat_limit():
    g = sc.schwarzschild_metric()
    assert g.shape == (4, 4)
    assert g.subs(sc.M, 0) == sp.diag(-1, 1, sc.R ** 2, sc.R ** 2 * sp.sin(sc.TH) ** 2)


def test_christoffel_symmetry_and_known_values():
    g = sc.schwarzschild_metric()
    gam = sc.christoffel(g)
    for a in range(4):
        for b in range(4):
            for c in range(4):
                assert sp.simplify(gam[a][b][c] - gam[a][c][b]) == 0
    assert sp.simplify(gam[1][0][0] - sc.M * (sc.R - 2 * sc.M) / sc.R ** 3) == 0
    assert sp.simplify(gam[2][1][2] - 1 / sc.R) == 0


def test_ricci_flat_and_kretschmann():
    g = sc.schwarzschild_metric()
    riem = sc.riemann(sc.christoffel(g))
    assert sc.ricci(riem) == sp.zeros(4, 4)
    assert sp.simplify(sc.kretschmann(g, riem) - 48 * sc.M ** 2 / sc.R ** 6) == 0


def test_antisymmetry_helper():
    g = sc.schwarzschild_metric()
    riem = sc.riemann(sc.christoffel(g))
    assert sc.component(riem, 0, 1, 1, 0) == -riem[(0, 1, 0, 1)]
    assert sc.component(riem, 2, 3, 1, 1) == 0
