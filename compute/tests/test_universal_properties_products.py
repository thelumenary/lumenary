from itertools import product

import universal_properties_products as up


def test_maps_counts():
    assert len(up.maps(range(2), range(3))) == 9
    assert up.maps([], range(3)) == [{}]
    assert up.maps(range(2), []) == []


def test_pairing_recovers_components():
    f = {0: "a", 1: "b"}
    g = {0: 1, 1: 2}
    h = up.pairing(f, g)
    assert h == {0: ("a", 1), 1: ("b", 2)}
    assert {x: h[x][0] for x in h} == f and {x: h[x][1] for x in h} == g


def test_true_product_has_unique_factorisations():
    A, B = [0, 1], [0, 1, 2]
    P = list(product(A, B))
    for nx in range(3):
        counts = up.factorisation_counts(range(nx), A, B, P,
                                         lambda z: z[0], lambda z: z[1])
        assert counts == {1}


def test_candidates_behave_as_claimed():
    A, B = ["a0", "a1"], ["b0", "b1", "b2"]
    (n1, P1, p1, q1), (n2, P2, p2, q2), (n3, P3, p3, q3) = up.candidates(A, B)
    X = range(2)
    assert up.factorisation_counts(X, A, B, P1, p1, q1) == {1}
    assert up.factorisation_counts(X, A, B, P2, p2, q2) == {4}
    counts3 = up.factorisation_counts(X, A, B, P3, p3, q3)
    assert 0 in counts3 and max(counts3) > 1
    # the numbers model really is a bijection onto A x B
    assert sorted((p1(k), q1(k)) for k in P1) == sorted(product(A, B))


def test_disjoint_union_never_a_product_by_counting():
    # 5 elements cannot map onto the 6 pairs, so some (f, g) never factors
    A, B = ["a0", "a1"], ["b0", "b1", "b2"]
    _, P3, p3, q3 = up.candidates(A, B)[2]
    hit = {(p3(z), q3(z)) for z in P3}
    assert len(hit) < len(A) * len(B)
