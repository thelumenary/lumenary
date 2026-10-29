import abelian_categories_free_cokernels as fc


def test_det_small_matrices():
    assert fc.det([[3]]) == 3
    assert fc.det([[1, 2], [3, 4]]) == -2
    assert fc.det([[2, 0, 0], [0, 3, 0], [0, 0, 5]]) == 30
    assert fc.det([[0, 1, 0], [1, 0, 0], [0, 0, 1]]) == -1


def test_invariant_factors_examples():
    assert fc.invariant_factors([[2]]) == [2]
    assert fc.invariant_factors([[0]]) == []
    assert fc.invariant_factors([[2, 0], [0, 3]]) == [1, 6]   # Z/2 + Z/3 = Z/6
    assert fc.invariant_factors([[2, 4], [6, 8]]) == [2, 4]
    assert fc.invariant_factors([[1, 2], [2, 4]]) == [1]      # rank one


def test_invariant_factors_divide_each_other_and_multiply_to_det():
    import itertools
    for a, b, c, d in itertools.product(range(-3, 4), repeat=4):
        m = [[a, b], [c, d]]
        f = fc.invariant_factors(m)
        assert all(f[i + 1] % f[i] == 0 for i in range(len(f) - 1))
        if fc.det(m) != 0:
            assert len(f) == 2 and f[0] * f[1] == abs(fc.det(m))


def test_cokernels_and_index():
    (tors, free), f_rank = fc.cokernels([[2]])
    assert tors == [2] and free == 0 and f_rank == 0
    (tors, free), f_rank = fc.cokernels([[0]])
    assert tors == [] and free == 1 and f_rank == 1
    assert fc.coimage_to_image_index([[2, 0], [0, 2]]) == 4
    assert fc.coimage_to_image_index([[1, 1], [0, 1]]) == 1   # invertible


def test_describe():
    assert fc.describe([], 0) == "0"
    assert fc.describe([2], 1) == "Z/2 + Z"
