import quotients_coset_products as qc


def test_group_and_subgroup_counts():
    counts = {}
    for name, gens in qc.groups():
        group = qc.closure(gens)
        counts[name] = (len(group), len(qc.subgroups(group)))
    assert counts == {"S3": (6, 6), "D4": (8, 10), "A4": (12, 10)}


def test_well_defined_iff_normal():
    for _, gens in qc.groups():
        group = qc.closure(gens)
        for sub in qc.subgroups(group):
            assert qc.is_normal(sub, group) == (qc.product_witness(sub, group) is None)


def test_witness_is_genuine():
    s3 = qc.closure([(1, 0, 2), (1, 2, 0)])
    sub = qc.closure([(1, 0, 2)])
    a, a2, b = qc.product_witness(sub, s3)
    assert qc.coset(a, sub) == qc.coset(a2, sub)
    assert qc.coset(qc.compose(a, b), sub) != qc.coset(qc.compose(a2, b), sub)


def test_quotient_orders():
    d4 = qc.closure([(1, 2, 3, 0), (0, 3, 2, 1)])
    centre = qc.closure([(2, 3, 0, 1)])
    assert qc.is_normal(centre, d4)
    # D4 / <r^2> is the Klein four-group: three elements of order 2
    assert qc.quotient_orders(centre, d4) == [(1, 1), (2, 3)]
    a4 = qc.closure([(1, 2, 0, 3), (1, 0, 3, 2)])
    v4 = qc.closure([(1, 0, 3, 2), (2, 3, 0, 1)])
    assert qc.quotient_orders(v4, a4) == [(1, 1), (3, 2)]


def test_normal_subgroup_counts():
    expected = {"S3": 3, "D4": 6, "A4": 3}
    for name, gens in qc.groups():
        group = qc.closure(gens)
        assert sum(qc.is_normal(s, group) for s in qc.subgroups(group)) == expected[name]
