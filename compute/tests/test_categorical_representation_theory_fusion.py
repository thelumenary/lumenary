import math

import categorical_representation_theory_fusion as cf


def test_group_orders_and_identity_first():
    sizes = {name: len(cf.generate(gens)) for name, gens in cf.GROUPS.items()}
    assert sizes == {"S3": 6, "D4": 8, "Q8": 8}
    for gens in cf.GROUPS.values():
        assert cf.generate(gens)[0] == cf.ONE


def test_linear_characters_counts():
    # |G / [G, G]| one-dimensional characters: 2 for S3, 4 for D4 and Q8.
    counts = {name: len(cf.linear_characters(cf.generate(g)))
              for name, g in cf.GROUPS.items()}
    assert counts == {"S3": 2, "D4": 4, "Q8": 4}


def test_character_tables_are_complete_and_orthonormal():
    for gens in cf.GROUPS.values():
        group, chars = cf.character_table(gens)
        assert sum(c[0] ** 2 for c in chars) == len(group)
        for i, a in enumerate(chars):
            for j, b in enumerate(chars):
                assert cf.inner(a, b) == (1 if i == j else 0)


def test_fusion_rings():
    for gens in cf.GROUPS.values():
        _, chars = cf.character_table(gens)
        n = cf.fusion(chars)
        assert cf.check_fusion_ring(n)
        dims = [c[0] for c in chars]
        r = range(len(dims))
        for i in r:
            for j in r:
                assert dims[i] * dims[j] == sum(n[i][j][k] * dims[k] for k in r)
    _, s3 = cf.character_table(cf.GROUPS["S3"])
    assert [int(v) for v in cf.fusion(s3)[2][2]] == [1, 1, 1]


def test_d4_q8_same_fusion_different_groups():
    _, d4 = cf.character_table(cf.GROUPS["D4"])
    _, q8 = cf.character_table(cf.GROUPS["Q8"])
    assert cf.isomorphic_fusion(cf.fusion(d4), cf.fusion(q8))
    _, s3 = cf.character_table(cf.GROUPS["S3"])
    assert not cf.isomorphic_fusion(cf.fusion(d4), cf.fusion(s3))
    order2 = lambda gens: sum(1 for g in cf.generate(gens)
                              if cf.element_order(g) == 2)
    assert order2(cf.GROUPS["D4"]) == 5 and order2(cf.GROUPS["Q8"]) == 1


def test_fp_dimension():
    assert abs(cf.fp_dimension([[0, 1], [1, 1]]) - (1 + math.sqrt(5)) / 2) < 1e-12
    # Rep(S3) regular object: FPdim of the standard representation is 2.
    _, s3 = cf.character_table(cf.GROUPS["S3"])
    n = cf.fusion(s3)
    mat = [[float(n[2][j][k]) for j in range(3)] for k in range(3)]
    assert abs(cf.fp_dimension(mat) - 2) < 1e-9
    # Ising: sigma (x) sigma = 1 + psi, FPdim sqrt 2.
    ising_sigma = [[0, 1, 0], [1, 0, 1], [0, 1, 0]]
    assert abs(cf.fp_dimension(ising_sigma) - math.sqrt(2)) < 1e-9
