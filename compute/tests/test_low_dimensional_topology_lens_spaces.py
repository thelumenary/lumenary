import low_dimensional_topology_lens_spaces as ls


def test_units_and_inverses():
    assert ls.units(7) == [1, 2, 3, 4, 5, 6]
    assert ls.units(12) == [1, 5, 7, 11]
    for p in (5, 7, 12, 15):
        for q in ls.units(p):
            assert q * ls.inverse(q, p) % p == 1


def test_classic_examples():
    assert ls.homotopy_equivalent(7, 1, 2) and not ls.homeomorphic(7, 1, 2)
    assert not ls.homotopy_equivalent(5, 1, 2)
    assert ls.homeomorphic(5, 1, 4)          # 4 = -1 mod 5
    assert ls.homeomorphic(7, 2, 4)          # 4 = 2^(-1) mod 7


def test_homeomorphism_implies_homotopy_equivalence():
    for p in range(2, 30):
        for q in ls.units(p):
            for r in ls.units(p):
                if ls.homeomorphic(p, q, r):
                    assert ls.homotopy_equivalent(p, q, r)


def test_relations_are_symmetric():
    for p in range(2, 25):
        for q in ls.units(p):
            for r in ls.units(p):
                assert ls.homeomorphic(p, q, r) == ls.homeomorphic(p, r, q)
                assert ls.homotopy_equivalent(p, q, r) == \
                    ls.homotopy_equivalent(p, r, q)


def test_class_counts():
    assert len(ls.classes(7, ls.homeomorphic)) == 2
    assert len(ls.classes(7, ls.homotopy_equivalent)) == 1
    assert len(ls.classes(5, ls.homotopy_equivalent)) == 2
    # p = 11: {1, 10}, {2, 5, 6, 9}, {3, 4, 7, 8}
    assert len(ls.classes(11, ls.homeomorphic)) == 3
    assert len(ls.classes(13, ls.homeomorphic)) == 4


def test_torsion_moduli_distinguish_and_agree():
    assert ls.torsion_moduli(7, 2) == ls.torsion_moduli(7, 4)
    assert ls.torsion_moduli(7, 1) != ls.torsion_moduli(7, 2)
    assert ls.torsion_moduli(7, 1) == ls.torsion_moduli(7, 6)
    # product of |z^k - 1| over k = 1..p-1 is p, so the product of moduli is p^2
    prod = 1.0
    for v in ls.torsion_moduli(7, 3):
        prod *= v
    assert abs(prod - 49) < 1e-3
