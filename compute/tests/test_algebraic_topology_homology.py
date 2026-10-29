import algebraic_topology_homology as ah


def test_smith_diagonal_known_matrices():
    assert ah.smith_diagonal([[2, 4], [6, 8]]) == [2, 4]
    assert ah.smith_diagonal([[0, 0], [0, 0]]) == []
    assert ah.smith_diagonal([[2]]) == [2]
    # diag(2, 3) has Smith form diag(1, 6)
    assert ah.smith_diagonal([[2, 0], [0, 3]]) == [1, 6]
    # invariant factors divide each other
    d = ah.smith_diagonal([[4, 6, 2], [2, 8, 4], [6, 2, 10]])
    assert all(d[i + 1] % d[i] == 0 for i in range(len(d) - 1))


def test_boundary_of_boundary_is_zero():
    for tris in ah.SURFACES.values():
        _, _, d1, d2 = ah.boundary_matrices(tris)
        for i in range(len(d1)):
            for k in range(len(d2[0])):
                assert sum(d1[i][j] * d2[j][k] for j in range(len(d2))) == 0


def test_homology_of_the_four_surfaces():
    expected = {
        "sphere S^2": ((1, 0, 1), []),
        "torus T^2": ((1, 2, 1), []),
        "Klein bottle": ((1, 1, 0), [2]),
        "proj. plane RP^2": ((1, 0, 0), [2]),
    }
    for name, (betti, torsion) in expected.items():
        b, t, _, _ = ah.homology(ah.SURFACES[name])
        assert b == betti and t == torsion, name


def test_mod2_betti_numbers_and_euler_characteristic():
    for name, tris in ah.SURFACES.items():
        b, _, b2, (v, e, f) = ah.homology(tris)
        chi = v - e + f
        assert chi == b[0] - b[1] + b[2] == b2[0] - b2[1] + b2[2]
    assert ah.homology(ah.SURFACES["proj. plane RP^2"])[2] == (1, 1, 1)
    assert ah.homology(ah.SURFACES["Klein bottle"])[2] == (1, 2, 1)


def test_grid_triangulations_are_simplicial():
    for twist in (False, True):
        tris = ah.grid_surface(twist)
        assert len(set(tris)) == 18
        edges = {e for t in tris for e in ah.combinations(t, 2)}
        # every edge of a closed surface lies in exactly two triangles
        for e in edges:
            assert sum(1 for t in tris if set(e) <= set(t)) == 2


def test_describe():
    assert ah.describe((1, 1, 0), [2]) == "Z | Z+Z/2 | 0"
    assert ah.describe((1, 2, 1), []) == "Z | Z^2 | Z"
