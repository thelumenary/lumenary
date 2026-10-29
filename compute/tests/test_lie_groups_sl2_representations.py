from fractions import Fraction

import pytest

import lie_groups_sl2_representations as ls


@pytest.mark.parametrize("n", range(7))
def test_relations_and_casimir(n):
    assert ls.relations_hold(n)
    c = ls.casimir(n)
    for i in range(n + 1):
        for j in range(n + 1):
            assert c[i][j] == (Fraction(n * (n + 2), 2) if i == j else 0)


def test_weights_and_irrep_shape():
    e, f, h = ls.irrep(3)
    assert [h[k][k] for k in range(4)] == [3, 1, -1, -3]
    assert all(x == 0 for x in e[0][:1])  # e kills the highest weight vector v_0
    assert f[3] == [0, 0, 1, 0]


@pytest.mark.parametrize("m, n", [(1, 1), (2, 1), (3, 3), (4, 1)])
def test_clebsch_gordan(m, n):
    parts = ls.decompose(ls.tensor_weights(m, n))
    assert parts == list(range(m + n, abs(m - n) - 1, -2))
    assert sum(p + 1 for p in parts) == (m + 1) * (n + 1)


def test_decompose_rejects_non_weights():
    with pytest.raises(ValueError):
        ls.decompose([1, 0])


def test_sl3_roots():
    assert ls.ad_check((3, 1, -4)) and ls.ad_check((0, 5, -5))
    assert len(ls.sl3_roots()) == 6
    simple = [ls.root_vector(0, 1), ls.root_vector(1, 2)]
    assert ls.cartan_matrix(simple) == [[2, -1], [-1, 2]]
