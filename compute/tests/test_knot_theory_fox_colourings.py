import knot_theory_fox_colourings as kf


def test_arcs_of_standard_diagrams():
    assert len(set(kf.arcs(kf.KNOTS["3_1"]).values())) == 3
    assert len(set(kf.arcs(kf.KNOTS["4_1"]).values())) == 4
    assert len(set(kf.arcs(kf.KNOTS["unknot (1 kink)"]).values())) == 1


def test_colouring_matrix_rows_sum_to_zero():
    # constant colourings always satisfy 2x = y + z
    for pd in kf.KNOTS.values():
        for row in kf.colouring_matrix(pd):
            assert sum(row) == 0


def test_determinants():
    expected = {"unknot (1 kink)": 1, "3_1": 3, "4_1": 5, "5_1": 5, "5_2": 7, "6_1": 9}
    for name, det in expected.items():
        assert kf.knot_determinant(kf.KNOTS[name]) == det


def test_counts_match_brute_force():
    for name in ("3_1", "4_1", "5_2"):
        for p in (3, 5):
            pd = kf.KNOTS[name]
            assert kf.count_colourings(pd, p) == kf.brute_force_count(pd, p)


def test_nontrivial_colouring_iff_p_divides_det():
    for name, pd in kf.KNOTS.items():
        det = kf.knot_determinant(pd)
        for p in (3, 5, 7):
            assert (kf.count_colourings(pd, p) > p) == (det % p == 0), (name, p)


def test_rank_and_determinant_helpers():
    assert kf.rank_mod_p([[1, 2], [2, 4]], 5) == 1
    assert kf.rank_mod_p([[1, 2], [3, 4]], 5) == 2
    assert kf.determinant([[2, -1], [-1, 2]]) == 3
    assert kf.determinant([[1, 2], [2, 4]]) == 0
