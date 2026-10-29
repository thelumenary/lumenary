import random

import modules_smith_normal_form as snf


def test_known_smith_forms():
    assert snf.smith_diagonal([[2, 0], [0, 3]]) == [1, 6]
    assert snf.smith_diagonal([[4, 6], [6, 4]]) == [2, 10]
    assert snf.smith_diagonal([[0, 0], [0, 0]]) == [0, 0]
    assert snf.smith_diagonal([[2, 4, 4], [-6, 6, 12], [10, -4, -16]]) == [2, 6, 12]


def test_cokernels():
    assert snf.cokernel([[2, 0], [0, 3]]) == (0, [6])
    assert snf.cokernel([[2, 4], [4, 8], [6, 12]]) == (2, [2])
    assert snf.cokernel([[1, 0], [0, 1]]) == (0, [])
    assert snf.cokernel([[0], [0]]) == (2, [])


def test_chain_and_minor_identity_on_random_matrices():
    rng = random.Random(7)
    for _ in range(100):
        m, n = rng.randint(1, 3), rng.randint(1, 3)
        mat = [[rng.randint(-6, 6) for _ in range(n)] for _ in range(m)]
        diag = snf.smith_diagonal(mat)
        assert len(diag) == min(m, n)
        assert snf.chain_ok(diag)
        assert snf.identity_ok(mat)


def test_order_of_finite_cokernel_is_abs_det():
    rng = random.Random(3)
    for _ in range(100):
        mat = [[rng.randint(-5, 5) for _ in range(3)] for _ in range(3)]
        d = snf.det(mat)
        free, tors = snf.cokernel(mat)
        if d:
            order = 1
            for t in tors:
                order *= t
            assert free == 0 and order == abs(d)
        else:
            assert free >= 1


def test_counting_abelian_groups():
    assert [snf.partitions(k) for k in range(7)] == [1, 1, 2, 3, 5, 7, 11]
    assert snf.groups_by_elementary_divisors(1) == 1
    assert snf.groups_by_elementary_divisors(8) == 3
    assert snf.groups_by_elementary_divisors(36) == 4
    for n in range(1, 80):
        assert snf.groups_by_elementary_divisors(n) == snf.groups_by_invariant_factors(n)


def test_chain_ok_rejects_bad_diagonals():
    assert not snf.chain_ok([2, 3])
    assert not snf.chain_ok([0, 2])
    assert snf.chain_ok([2, 4, 0])
