import random

import abelian_categories_snake as ac


def test_rank_mod_p():
    assert ac.rank([]) == 0
    assert ac.rank([[1, 0], [0, 1]]) == 2
    assert ac.rank([[1, 2], [2, 4]]) == 1          # dependent columns
    assert ac.rank([[5, 0]], p=5) == 0              # 5 = 0 in F_5
    assert ac.rank([[1, 1], [1, 4]], p=5) == 2


def test_kernel_basis_is_a_basis_of_the_kernel():
    rng = random.Random(3)
    for _ in range(50):
        m, n = rng.randint(1, 4), rng.randint(1, 5)
        mat = ac.random_matrix(m, n, rng)
        basis = ac.kernel_basis(mat, n)
        assert all(ac.apply(mat, v) == [0] * m for v in basis)
        assert ac.rank(basis) == len(basis)
        assert len(basis) == n - ac.rank(ac.columns(mat))


def test_is_exact_on_simple_sequences():
    # 0 -> F -> F -> 0 -> 0 -> 0 -> 0 with an isomorphism: exact
    assert ac.is_exact([1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0])
    # a non-injective first map is not exact
    assert not ac.is_exact([1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0])


def test_snake_sequences_are_exact():
    rng = random.Random(11)
    for _ in range(100):
        dims_in = [rng.randint(1, 3) for _ in range(4)]
        dims, ranks, zero = ac.snake_data(*dims_in, rng)
        assert zero
        assert ac.is_exact(dims, ranks)
        assert dims[0] - dims[1] + dims[2] - dims[3] + dims[4] - dims[5] == 0


def test_forgetting_delta_breaks_exactness():
    rng = random.Random(5)
    broken = 0
    for _ in range(100):
        dims, ranks, _ = ac.snake_data(2, 2, 2, 2, rng)
        if ranks[2] > 0:
            fake = ranks[:2] + [0] + ranks[3:]
            broken += not ac.is_exact(dims, fake)
    assert broken > 0


def test_identity_and_columns():
    assert ac.identity(2) == [[1, 0], [0, 1]]
    assert ac.columns([[1, 2], [3, 4]]) == [[1, 3], [2, 4]]
