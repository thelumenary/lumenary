from math import gcd

import products_coproducts_finite as pc


def test_maps_counts():
    assert len(pc.maps((0, 1), "abc")) == 9
    assert pc.maps((), "abc") == [{}]
    assert pc.maps((0,), ()) == []


def test_cartesian_product_has_unique_factorisations():
    A, B = (0, 1), ("a", "b", "c")
    cart = pc.candidates(A, B)[0]
    for n in range(4):
        assert pc.count_profile(A, B, tuple(range(n)), cart) == {1}


def test_fake_products_fail_uniqueness_or_existence():
    A, B = (0, 1), ("a", "b", "c")
    _, bigger, smaller = pc.candidates(A, B)
    for n in range(1, 3):
        assert pc.count_profile(A, B, tuple(range(n)), bigger) == {2 ** n}
        assert 0 in pc.count_profile(A, B, tuple(range(n)), smaller)


def test_universal_property_matches_hom_counting():
    # |Hom(X, A x B)| = |Hom(X, A)| * |Hom(X, B)|
    A, B, X = (0, 1), ("a", "b", "c"), (0, 1)
    P = pc.candidates(A, B)[0][1]
    assert len(pc.maps(X, P)) == len(pc.maps(X, A)) * len(pc.maps(X, B))


def test_meets_and_joins_in_divisibility_posets():
    divs = [d for d in range(1, 61) if 60 % d == 0]
    for a in divs:
        for b in divs:
            assert pc.glb(divs, pc.divides, a, b) == gcd(a, b)
            assert pc.lub(divs, pc.divides, a, b) == a * b // gcd(a, b)


def test_non_lattice_has_missing_products_and_coproducts():
    small = [2, 3, 12, 18]
    assert pc.lub(small, pc.divides, 2, 3) is None
    assert pc.glb(small, pc.divides, 12, 18) is None
    assert pc.glb(small, pc.divides, 2, 3) is None
    assert pc.glb(small, pc.divides, 2, 12) == 2
    assert pc.lub(small, pc.divides, 3, 18) == 18
