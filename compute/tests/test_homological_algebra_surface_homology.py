import homological_algebra_surface_homology as sh


def test_cell_complexes_have_dd_zero():
    for word in sh.WORDS.values():
        d2, d1 = sh.cell_complex(word)
        prod = sh.matmul(d1, d2)
        assert all(x == 0 for row in prod for x in row)


def test_vertex_counts():
    counts = {name: len(sh.cell_complex(w)[1]) for name, w in sh.WORDS.items()}
    assert counts == {"torus": 1, "Klein bottle": 1, "sphere": 3,
                      "projective plane": 2}


def test_integral_homology():
    assert sh.homology(sh.WORDS["torus"]) == ((1, 2, 1), {0: [], 1: [], 2: []})
    assert sh.homology(sh.WORDS["Klein bottle"]) == ((1, 1, 0), {0: [], 1: [2], 2: []})
    assert sh.homology(sh.WORDS["sphere"]) == ((1, 0, 1), {0: [], 1: [], 2: []})
    assert sh.homology(sh.WORDS["projective plane"]) == ((1, 0, 0), {0: [], 1: [2], 2: []})


def test_mod_p_betti_numbers():
    assert sh.homology(sh.WORDS["projective plane"], 2)[0] == (1, 1, 1)
    assert sh.homology(sh.WORDS["projective plane"], 3)[0] == (1, 0, 0)
    assert sh.homology(sh.WORDS["Klein bottle"], 2)[0] == (1, 2, 1)


def test_rank_and_smith():
    assert sh.rank([[2, 2]], 2) == 0
    assert sh.rank([[2, 2]]) == 1
    assert sh.smith_diagonal([[2, 4], [6, 8]]) == [2, 4]
    assert sh.torsion([[2], [2]]) == [2]
    assert sh.torsion([[-1, 1], [1, -1]]) == []
