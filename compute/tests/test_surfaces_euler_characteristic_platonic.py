import math

import surfaces_euler_characteristic_platonic as ex


def test_schlafli_solutions_are_the_five_solids():
    sols = ex.schlafli_solutions()
    assert sorted((p, q) for p, q, *_ in sols) == [(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)]
    for p, q, v, e, f in sols:
        assert v - e + f == 2
        assert p * f == 2 * e and q * v == 2 * e


def test_vertex_counts_and_edges():
    expected = {"tetrahedron": (4, 6), "cube": (8, 12), "octahedron": (6, 12),
                "dodecahedron": (20, 30), "icosahedron": (12, 30)}
    for solid, (v, e) in expected.items():
        pts = ex.SOLIDS[solid]
        assert len(pts) == v
        assert len(ex.edges(pts)) == e


def test_faces_and_euler_formula():
    expected_f = {"tetrahedron": 4, "cube": 6, "octahedron": 8, "dodecahedron": 12, "icosahedron": 20}
    for solid, f in expected_f.items():
        pts = ex.SOLIDS[solid]
        es = ex.edges(pts)
        fs = ex.faces(len(pts), es)
        assert len(fs) == f
        assert len(pts) - len(es) + len(fs) == 2


def test_cycles_on_small_graphs():
    square = [(0, 1), (1, 2), (2, 3), (3, 0)]
    assert ex.cycles(4, square, 3) == []
    assert len(ex.cycles(4, square, 4)) == 1
    k4 = [(a, b) for a in range(4) for b in range(a + 1, 4)]
    assert len(ex.cycles(4, k4, 3)) == 4
    assert len(ex.cycles(4, k4, 4)) == 3


def test_total_defect_is_four_pi_for_solids_and_zero_for_torus():
    for pts in ex.SOLIDS.values():
        fs = ex.faces(len(pts), ex.edges(pts))
        assert math.isclose(ex.total_defect(pts, fs), 4 * math.pi, rel_tol=1e-9)
    pts, fs = ex.picture_frame()
    assert len(pts) == 16 and len(fs) == 16 and len(ex.edges_of_faces(fs)) == 32
    assert abs(ex.total_defect(pts, fs)) < 1e-9


def test_angle():
    assert math.isclose(ex.angle((1, 0, 0), (0, 0, 0), (0, 1, 0)), math.pi / 2)
    assert math.isclose(ex.angle((1, 0, 0), (0, 0, 0), (1, 1, 0)), math.pi / 4)
