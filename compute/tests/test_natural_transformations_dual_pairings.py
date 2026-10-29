import pytest

import natural_transformations_dual_pairings as dp


def test_matrix_helpers():
    a = ((1, 2), (3, 4))
    assert dp.mat_mul(a, ((1, 0), (0, 1)), 5) == a
    assert dp.transpose(a) == ((1, 3), (2, 4))
    assert dp.det(a, 7) == (4 - 6) % 7
    assert dp.det(((2, 0, 0), (0, 3, 0), (0, 0, 4)), 5) == 24 % 5
    assert sum(1 for _ in dp.all_matrices(2, 3)) == 81


def test_primitive_roots():
    assert dp.primitive_root(2) == 1
    assert dp.primitive_root(3) == 2
    assert dp.primitive_root(5) == 2
    assert dp.primitive_root(7) == 3
    with pytest.raises(ValueError):
        dp.primitive_root(4)


def test_generators_generate_gl2_f3():
    gens = dp.gl_generators(2, 3)
    ident = ((1, 0), (0, 1))
    group, frontier = {ident}, [ident]
    while frontier:
        new = []
        for g in frontier:
            for h in gens:
                k = dp.mat_mul(g, h, 3)
                if k not in group:
                    group.add(k)
                    new.append(k)
        frontier = new
    assert len(group) == 48  # |GL_2(F_3)| = (9 - 1)(9 - 3)


def test_invariant_form_counts():
    assert dp.invariant_forms(1, 2) == [((1,),)]
    assert len(dp.invariant_forms(1, 3)) == 2
    assert dp.invariant_forms(1, 5) == []
    assert dp.invariant_forms(2, 2) == [((0, 1), (1, 0))]
    assert dp.invariant_forms(2, 3) == []
    assert dp.invariant_forms(3, 2) == []


def test_determinant_pairing_is_invariant_under_all_of_gl2_f2():
    j = ((0, 1), (1, 0))
    invertible = [g for g in dp.all_matrices(2, 2) if dp.det(g, 2)]
    assert len(invertible) == 6
    assert all(dp.invariant(j, g, 2) for g in invertible)


def test_dot_product_preserved_by_few_maps():
    assert dp.dot_preserving(2, 2) == (2, 6)
    assert dp.dot_preserving(2, 3) == (8, 48)
    assert dp.dot_preserving(2, 5) == (8, 480)
