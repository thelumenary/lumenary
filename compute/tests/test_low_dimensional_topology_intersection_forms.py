from fractions import Fraction

import low_dimensional_topology_intersection_forms as f


def test_e8_invariants():
    assert f.invariants(f.e8()) == (8, 8, 1, True)
    assert f.invariants(f.scale(f.e8(), -1)) == (8, -8, 1, True)


def test_hyperbolic_plane_needs_the_zero_pivot_step():
    assert f.invariants(f.H) == (2, 0, -1, True)
    assert f.invariants([[0, 0], [0, 0]])[0:3] == (2, 0, 0)


def test_k3_form():
    k3 = f.direct_sum(f.scale(f.e8(), -1), f.scale(f.e8(), -1), f.H, f.H, f.H)
    assert f.invariants(k3) == (22, -16, -1, True)


def test_signature_is_a_congruence_invariant():
    # P^T M P for an integer P with det 1 has the same invariants as M.
    m = [[1, 0, 0], [0, -1, 0], [0, 0, 1]]
    p = [[1, 2, 0], [0, 1, 3], [0, 0, 1]]
    pt = [list(r) for r in zip(*p)]
    mul = lambda a, b: [[sum(a[i][k] * b[k][j] for k in range(3))
                         for j in range(3)] for i in range(3)]
    q = mul(mul(pt, m), p)
    assert f.invariants(q)[:3] == f.invariants(m)[:3] == (3, 1, -1)


def test_diagonalise_product_is_determinant():
    m = [[2, 1], [1, 3]]
    d = f.diagonalise(m)
    assert d[0] * d[1] == Fraction(5)
    assert f.invariants(m) == (2, 2, 5, False)


def test_direct_sum_shape():
    m = f.direct_sum([[1]], f.H, f.e8())
    assert len(m) == 11 and all(len(r) == 11 for r in m)
    assert m[0][0] == 1 and m[1][2] == 1 and m[3][3] == 2
