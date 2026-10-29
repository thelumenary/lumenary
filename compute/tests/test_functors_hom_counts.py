from itertools import product

import pytest

import functors_hom_counts as fh


def is_group(group):
    elements, mul, one = group
    elems = set(elements)
    closed = all(mul(a, b) in elems for a, b in product(elements, repeat=2))
    assoc = all(mul(mul(a, b), c) == mul(a, mul(b, c))
                for a, b, c in product(elements, repeat=3))
    unit = all(mul(one, a) == a == mul(a, one) for a in elements)
    inverses = all(any(mul(a, b) == one for b in elements) for a in elements)
    return closed and assoc and unit and inverses


@pytest.mark.parametrize("name,group", fh.groups_of_order_8())
def test_order_8_groups_are_groups(name, group):
    assert len(group[0]) == 8
    assert is_group(group), name


def test_quaternion_relations():
    elements, mul, one = fh.quaternion8()
    i, j, k = (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)
    minus_one = (-1, 0, 0, 0)
    assert mul(i, j) == k and mul(j, i) == (0, 0, 0, -1)
    assert mul(i, i) == mul(j, j) == mul(k, k) == minus_one
    assert fh.power(fh.quaternion8(), i, 4) == one


def test_hom_counts_known_values():
    assert fh.hom_count_cyclic(fh.cyclic(6), 2) == 2   # 0 and 3
    assert fh.hom_count_cyclic(fh.cyclic(6), 3) == 3   # 0, 2, 4
    assert fh.hom_count_cyclic(fh.dihedral8(), 2) == 6
    assert fh.hom_count_cyclic(fh.quaternion8(), 2) == 2
    for name, group in fh.groups_of_order_8():
        assert fh.hom_count_cyclic(group, 1) == 1
        assert fh.hom_count_cyclic(group, 8) == 8   # Lagrange


def test_order_8_signatures_distinct_but_order_16_pair_not():
    sigs = {tuple(fh.hom_count_cyclic(g, n) for n in (1, 2, 4, 8))
            for _, g in fh.groups_of_order_8()}
    assert len(sigs) == 5
    z2, z4 = fh.cyclic(2), fh.cyclic(4)
    a = fh.direct_product(z4, z4)
    b = fh.direct_product(z2, fh.quaternion8())
    assert is_group(b)
    for n in range(1, 17):
        assert fh.hom_count_cyclic(a, n) == fh.hom_count_cyclic(b, n)


def test_commuting_pairs():
    z2, z4 = fh.cyclic(2), fh.cyclic(4)
    # abelian: every pair commutes
    assert fh.commuting_pairs(fh.direct_product(z4, z4)) == 256
    # |G| times the number of conjugacy classes: Q8 has 5, so Z/2 x Q8 has 10
    assert fh.commuting_pairs(fh.quaternion8()) == 8 * 5
    assert fh.commuting_pairs(fh.direct_product(z2, fh.quaternion8())) == 160
    assert fh.commuting_pairs(fh.dihedral8()) == 8 * 5
