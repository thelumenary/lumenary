import algebraic_geometry_points_mod_p as pm


def test_primes_between():
    assert pm.primes_between(3, 20) == [3, 5, 7, 11, 13, 17, 19]
    assert pm.primes_between(0, 3) == [2]


def test_projective_plane_size_and_distinct_points():
    for p in (2, 3, 5, 7):
        pts = pm.projective_points(p)
        assert len(pts) == p * p + p + 1
        assert len(set(pts)) == len(pts)


def test_conic_and_cusp_have_p_plus_one_points():
    for p in pm.primes_between(3, 40):
        assert pm.count_points(pm.conic, p) == p + 1
        assert pm.count_points(pm.cusp, p) == p + 1


def test_known_traces_of_frobenius():
    # #E(F_5) = 8: the point at infinity, (0,0), (1,0), (4,0), (2,+-1), (3,+-2)
    assert pm.count_points(pm.elliptic, 5) == 8
    assert pm.trace_of_frobenius(5) == -2
    assert pm.trace_of_frobenius(13) == 6
    assert pm.trace_of_frobenius(7) == 0


def test_hasse_bound_and_supersingular_primes():
    for p in pm.primes_between(3, 60):
        a = pm.trace_of_frobenius(p)
        assert a * a <= 4 * p
        if p % 4 == 3:
            assert a == 0
        else:
            assert pm.is_sum_of_two_squares_with(a // 2, p)


def test_line_has_p_plus_one_points():
    # a line in P^2(F_p) is a copy of P^1
    for p in (3, 5, 11):
        assert pm.count_points(lambda x, y, z: x + 2 * y + 3 * z, p) == p + 1
