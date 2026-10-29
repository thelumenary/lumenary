import vector_bundles_characteristic_classes_stiefel_whitney as sw


def test_total_class_of_small_projective_spaces():
    assert sw.total_sw(1) == [1, 0]          # RP^1 = S^1 is parallelisable
    assert sw.total_sw(2) == [1, 1, 1]       # w(RP^2) = 1 + a + a^2
    assert sw.total_sw(3) == [1, 0, 0, 0]    # RP^3 = SO(3) is parallelisable
    assert sw.total_sw(4) == [1, 1, 0, 0, 1]


def test_w_equals_one_iff_n_plus_one_is_power_of_two():
    for n in range(1, 64):
        trivial = not sw.nonzero_degrees(sw.total_sw(n))
        assert trivial == ((n + 1) & n == 0)


def test_inverse_and_multiply():
    for n in range(1, 20):
        w = sw.total_sw(n)
        assert sw.multiply(w, sw.inverse(w, n), n) == [1] + [0] * n
    # (1 + a)^(-1) = 1 + a + a^2 + ... in Z/2
    assert sw.inverse([1, 1, 0, 0, 0], 4) == [1, 1, 1, 1, 1]


def test_top_class_is_euler_characteristic_mod_2():
    for n in range(1, 30):
        assert sw.total_sw(n)[n] == (1 if n % 2 == 0 else 0)


def test_whitney_immersion_bound_for_powers_of_two():
    for r in range(1, 6):
        n = 2 ** r
        assert sw.immersion_bound(n) == n - 1
    assert sw.immersion_bound(3) == 0


def test_ranges():
    assert sw.ranges([1, 2, 3, 8]) == "1-3,8"
    assert sw.ranges([]) == "-"
    assert sw.ranges([2, 4]) == "2,4"
