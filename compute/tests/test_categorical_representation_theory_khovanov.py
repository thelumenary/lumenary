import categorical_representation_theory_khovanov as kh

TREFOIL = kh.KNOTS["trefoil 3_1"]
FIG8 = kh.KNOTS["figure-eight 4_1"]


def mirror(pd):
    """Mirror image: the old over-strand becomes the under-strand.

    The new list starts at the incoming end of the old over-strand: l if it
    ran l -> j (a positive crossing), j if it ran j -> l.
    """
    return [(l, i, j, k) if kh.crossing_sign((i, j, k, l)) > 0
            else (j, k, l, i) for i, j, k, l in pd]


def test_crossing_signs():
    assert [kh.crossing_sign(x) for x in TREFOIL] == [-1, -1, -1]
    assert sum(kh.crossing_sign(x) for x in FIG8) == 0
    assert [kh.crossing_sign(x) for x in mirror(TREFOIL)] == [1, 1, 1]


def test_circle_counts_of_extreme_smoothings():
    # Trefoil: all-0 and all-1 smoothings give 3 and 2 circles (one of them
    # is the Seifert smoothing).
    counts = sorted(len(kh.circles(TREFOIL, s)) for s in [(0, 0, 0), (1, 1, 1)])
    assert counts == [2, 3]
    for s in [(0, 1, 0), (1, 0, 1)]:
        labels = set().union(*kh.circles(TREFOIL, s))
        assert labels == set(range(1, 7))


def test_d_squared_zero():
    for pd in (TREFOIL, FIG8, mirror(TREFOIL)):
        assert kh.d_squared_is_zero(pd)


def test_jones_polynomials():
    chain, _ = kh.khovanov(TREFOIL)
    assert kh.euler(chain) == {-9: -1, -5: 1, -3: 1, -1: 1}
    chain, _ = kh.khovanov(mirror(TREFOIL))
    assert kh.euler(chain) == {1: 1, 3: 1, 5: 1, 9: -1}  # Bar-Natan's table
    chain, _ = kh.khovanov(FIG8)
    assert kh.euler(chain) == {-5: 1, 5: 1}


def test_khovanov_homology_matches_known_values():
    _, h = kh.khovanov(mirror(TREFOIL))
    assert h == {(0, 1): 1, (0, 3): 1, (2, 5): 1, (3, 9): 1}
    _, h = kh.khovanov(FIG8)
    assert h == {(-2, -5): 1, (-1, -1): 1, (0, -1): 1, (0, 1): 1,
                 (1, 1): 1, (2, 5): 1}


def test_euler_characteristic_of_homology_equals_jones():
    for pd in (TREFOIL, FIG8, mirror(FIG8)):
        chain, h = kh.khovanov(pd)
        assert kh.euler(h) == kh.euler(chain)


def test_rank_and_formatting():
    assert kh.rank([[1, 2], [2, 4]]) == 1
    assert kh.rank([[0, 0], [0, 0]]) == 0
    assert kh.show_poly({-5: 1, 5: 1}) == "q^-5 + q^5"
    assert kh.show_poly({-9: -1, -1: 2}) == "-q^-9 + 2q^-1"
