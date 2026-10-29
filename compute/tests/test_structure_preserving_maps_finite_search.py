from math import gcd

import structure_preserving_maps_finite_search as sp


def test_tables_are_closed_and_have_identities():
    for s in [sp.cyclic(5), sp.klein(), sp.rectangle(), sp.units_mod5()]:
        elems, table = s
        assert len(table) == len(elems) ** 2
        assert set(table.values()) <= set(elems)
        assert sp.identity_element(s) is not None
    assert sp.identity_element(sp.rectangle()) == (0, 1, 2, 3)
    assert sp.identity_element(sp.units_mod5()) == 1


def test_preserves_detects_good_and_bad_maps():
    _, t6 = sp.cyclic(6)
    _, t3 = sp.cyclic(3)
    reduce = {x: x % 3 for x in range(6)}
    shift = {x: (x + 1) % 3 for x in range(6)}
    assert sp.preserves(reduce, t6, t3)
    assert not sp.preserves(shift, t6, t3)


def test_homomorphism_counts_match_gcd():
    for m in range(1, 6):
        for n in range(1, 6):
            assert len(sp.homomorphisms(sp.cyclic(m), sp.cyclic(n))) == gcd(m, n)


def test_homomorphisms_are_multiples_of_f1():
    # Z/4 -> Z/6: f(1) must satisfy 4 f(1) = 0 mod 6, so f(1) is 0 or 3.
    homs = sp.homomorphisms(sp.cyclic(4), sp.cyclic(6))
    assert sorted(f[1] for f in homs) == [0, 3]
    for f in homs:
        assert all(f[k] == (k * f[1]) % 6 for k in range(4))


def test_isomorphism_counts():
    z4, v, rect, u5 = sp.cyclic(4), sp.klein(), sp.rectangle(), sp.units_mod5()
    assert len(sp.isomorphisms(z4, v)) == 0
    assert len(sp.isomorphisms(z4, u5)) == 2   # 1 -> 2 or 1 -> 3
    assert len(sp.isomorphisms(v, rect)) == 6  # = automorphisms of the Klein group
    assert len(sp.isomorphisms(z4, z4)) == 2
    assert sp.isomorphisms(z4, sp.cyclic(5)) == []  # different sizes


def test_discrete_logarithm_isomorphism():
    # k -> 2^k mod 5 turns addition mod 4 into multiplication mod 5.
    f = {k: pow(2, k, 5) for k in range(4)}
    assert f in sp.isomorphisms(sp.cyclic(4), sp.units_mod5())


def test_invariant():
    assert sp.squares_to_identity(sp.cyclic(4)) == 2
    assert sp.squares_to_identity(sp.klein()) == 4
    assert sp.squares_to_identity(sp.rectangle()) == 4
    assert sp.squares_to_identity(sp.units_mod5()) == 2
