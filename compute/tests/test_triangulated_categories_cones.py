import random

import triangulated_categories_cones as tc


def test_rank_and_nullspace():
    assert tc.rank([[1, 2], [2, 4]]) == 1
    assert tc.rank([[1, 0], [0, 1]]) == 2
    assert tc.rank([]) == 0
    basis = tc.nullspace([[1, 1, 0]], 3)
    assert len(basis) == 2
    for v in basis:
        assert (v[0] + v[1]) % tc.P == 0


def test_inverse_is_inverse():
    rng = random.Random(1)
    for k in (1, 2, 3, 4):
        m = tc.random_invertible(rng, k)
        prod = tc.matmul(m, tc.inverse(m))
        assert prod == [[int(i == j) for j in range(k)] for i in range(k)]


def test_random_complex_squares_to_zero():
    rng = random.Random(7)
    for _ in range(30):
        dims, d = tc.random_complex(rng)
        for n in range(len(d) - 1):
            assert not any(map(any, tc.matmul(d[n + 1], d[n])))


def test_chain_map_commutes_with_differentials():
    rng = random.Random(11)
    for _ in range(30):
        x, y = tc.random_complex(rng), tc.random_complex(rng)
        f = tc.random_chain_map(rng, x, y)
        (dx, ddx), (dy, ddy) = x, y
        for n in range(len(ddx)):
            for i in range(dy[n + 1]):
                for j in range(dx[n]):
                    lhs = sum(ddy[n][i][k] * f[n][k][j] for k in range(dy[n]))
                    rhs = sum(f[n + 1][i][k] * ddx[n][k][j]
                              for k in range(dx[n + 1]))
                    assert (lhs - rhs) % tc.P == 0


def test_cone_of_identity_is_acyclic_and_cone_of_zero_splits():
    rng = random.Random(5)
    for _ in range(20):
        x = tc.random_complex(rng)
        c = tc.cone(x, x, tc.identity_map(x))
        assert sum(tc.cohomology(c)) == 0
        zero = [[[0] * k for _ in range(k)] for k in x[0]]
        hz = tc.cohomology(tc.cone(x, x, zero))
        hx = tc.cohomology(x)
        # cone(0 : X -> X) = X + X[1], so H^n(C) = H^n(X) + H^(n+1)(X).
        hx_ext = [0] + hx + [0]
        assert hz == [hx_ext[n + 1] + hx_ext[n] for n in range(len(hz))]


def test_long_exact_sequence_dimension_formula():
    rng = random.Random(3)
    for _ in range(40):
        x, y = tc.random_complex(rng), tc.random_complex(rng)
        f = tc.random_chain_map(rng, x, y)
        hx, hy = tc.cohomology(x), tc.cohomology(y)
        hc = tc.cohomology(tc.cone(x, y, f))
        rk = [tc.rank_on_cohomology(x, y, f, n) for n in range(4)] + [0]
        assert hc[0] == hx[0] - rk[0]
        for n in range(4):
            assert hc[n + 1] == hy[n] - rk[n] + (hx + [0])[n + 1] - rk[n + 1]


def test_fill_in_count_is_p():
    for p in (2, 3, 5, 7):
        assert tc.fill_in_count(p) == p
