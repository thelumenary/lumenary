import sympy as sp

import complex_kahler_geometry_kahler_condition as kc

Z, ZB = kc.Z, kc.ZB


def test_flat_and_fubini_study_are_kahler():
    named = dict(kc.metrics())
    assert kc.kahler_defects(named["flat"]) == []
    assert kc.kahler_defects(named["Fubini-Study"]) == []


def test_every_potential_gives_a_kahler_metric():
    # d_k d_i dbar_j phi is symmetric in i, k: any potential works
    phi = Z[0] ** 2 * ZB[0] ** 2 + sp.exp(Z[1] * ZB[1]) + Z[0] * ZB[1] + Z[1] * ZB[0]
    assert kc.kahler_defects(kc.from_potential(phi)) == []


def test_hopf_metric_is_hermitian_scale_invariant_not_kahler():
    g = dict(kc.metrics())["Hopf |dz|^2/|z|^2"]
    assert kc.is_hermitian_symbolically(g)
    assert kc.scale_invariant(g)
    defects = kc.kahler_defects(g)
    assert len(defects) == 4
    norm2 = Z[0] * ZB[0] + Z[1] * ZB[1]
    assert sp.simplify(dict(defects)[(1, 1, 2)] + ZB[1] / norm2 ** 2) == 0


def test_non_hermitian_matrix_is_detected():
    g = sp.Matrix([[1, Z[0]], [Z[0], 1]])
    assert not kc.is_hermitian_symbolically(g)


def test_fubini_study_entries_and_area():
    fs = dict(kc.metrics())["Fubini-Study"]
    norm2 = 1 + Z[0] * ZB[0] + Z[1] * ZB[1]
    assert sp.simplify(fs[0, 0] - (1 + Z[1] * ZB[1]) / norm2 ** 2) == 0
    assert sp.simplify(fs[0, 1] + ZB[0] * Z[1] / norm2 ** 2) == 0
    assert kc.fubini_study_area_cp1() == sp.pi
