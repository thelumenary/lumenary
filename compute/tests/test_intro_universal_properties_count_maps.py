from itertools import product

import intro_universal_properties_count_maps as up


def test_all_functions_counts():
    assert len(up.all_functions(("x", "y"), up.A)) == 4
    assert len(up.all_functions(("x", "y", "z"), up.B)) == 27
    assert up.all_functions((), up.A) == [()]  # exactly one map from the empty set


def test_pairs_are_a_product():
    name, P, p, q = up.candidates()[0]
    assert name.startswith("ordered pairs")
    for size in range(4):
        assert up.is_product_on(tuple(range(size)), P, p, q)


def test_unique_h_is_the_pairing():
    _, P, p, q = up.candidates()[0]
    X = ("x", "y", "z")
    f, g = ("red", "blue", "red"), (2, 2, 3)
    matches = [h for h in product(P, repeat=3)
               if all(p[h[i]] == f[i] and q[h[i]] == g[i] for i in range(3))]
    assert matches == [tuple(zip(f, g))]
    assert up.count_compatible(X, P, p, q, f, g) == 1


def test_numbers_one_to_six_form_a_product():
    _, P, p, q = up.candidates()[1]
    assert up.is_product_on(("x",), P, p, q)
    assert up.is_product_on(("x", "y", "z"), P, p, q)
    # The compatible bijection P -> A x B is k -> (p(k), q(k)).
    assert sorted((p[k], q[k]) for k in P) == sorted(product(up.A, up.B))


def test_fake_products_fail_in_the_expected_way():
    X = ("x", "y")
    _, P1, p1, q1 = up.candidates()[2]
    prof1 = up.profile(X, P1, p1, q1)
    assert prof1[0] == 32 and prof1[1] == 4  # existence fails unless g is constant 1
    _, P2, p2, q2 = up.candidates()[3]
    prof2 = up.profile(X, P2, p2, q2)
    assert dict(prof2) == {4: 36}  # 2 choices of the extra bit at each of 2 points
    assert not up.is_product_on(X, P1, p1, q1)
    assert not up.is_product_on(X, P2, p2, q2)


def test_counting_identity():
    pairs = up.candidates()[0][1]
    for n in range(4):
        dom = tuple(range(n))
        lhs = len(up.all_functions(dom, pairs))
        rhs = len(up.all_functions(dom, up.A)) * len(up.all_functions(dom, up.B))
        assert lhs == rhs == 6 ** n
