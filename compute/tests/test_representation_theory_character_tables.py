import representation_theory_character_tables as ct


def groups():
    return {name: (g, kind) for name, (g, kind) in ct.build_groups().items()}


def test_group_orders_and_classes():
    gs = groups()
    assert len(gs["S3"][0].elems) == 6 and len(gs["S3"][0].classes) == 3
    assert len(gs["S4"][0].elems) == 24 and len(gs["S4"][0].classes) == 5
    assert len(gs["D4"][0].elems) == 8 and len(gs["D4"][0].classes) == 5
    assert len(gs["Q8"][0].elems) == 8 and len(gs["Q8"][0].classes) == 5


def test_tables_are_complete_and_orthonormal():
    for name, (g, kind) in groups().items():
        table = ct.character_table(g, kind)
        assert len(table) == len(g.classes), name
        assert sum(row[0] ** 2 for row in table) == len(g.elems), name
        for a in table:
            for b in table:
                assert g.inner(a, b) == (1 if a == b else 0), name


def test_s3_table():
    g, kind = groups()["S3"]
    assert ct.character_table(g, kind) == [(1, 1, 1), (1, -1, 1), (2, 0, -1)]


def test_s4_degrees():
    g, kind = groups()["S4"]
    assert sorted(row[0] for row in ct.character_table(g, kind)) == [1, 1, 2, 3, 3]


def test_d4_q8_same_table_but_not_isomorphic():
    gs = groups()
    d4, q8 = gs["D4"][0], gs["Q8"][0]
    td, tq = ct.character_table(d4, "perm"), ct.character_table(q8, "matrix")
    assert ct.same_table(d4, q8, td, tq)
    assert sum(1 for x in d4.elems if d4.order(x) == 2) == 5
    assert sum(1 for x in q8.elems if q8.order(x) == 2) == 1


def test_coset_character_and_sign():
    g, _ = groups()["S3"]
    assert g.coset_character([g.one]) == (6, 0, 0)       # regular character
    assert ct.sign((1, 0, 2)) == -1 and ct.sign((1, 2, 0)) == 1


def test_frobenius_schur_indicators_distinguish_d4_q8():
    gs = groups()
    d4, q8 = gs["D4"][0], gs["Q8"][0]
    chi_d4 = next(r for r in ct.character_table(d4, "perm") if r[0] == 2)
    chi_q8 = next(r for r in ct.character_table(q8, "matrix") if r[0] == 2)
    assert ct.fs_indicator(d4, chi_d4) == 1
    assert ct.fs_indicator(q8, chi_q8) == -1
    triv = tuple(1 for _ in d4.classes)
    assert ct.fs_indicator(d4, triv) == 1
