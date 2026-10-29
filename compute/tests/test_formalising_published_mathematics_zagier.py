import formalising_published_mathematics_zagier as z


def test_zagier_set_small_cases():
    assert z.zagier_set(5) == [(1, 1, 1)]
    assert z.zagier_set(13) == [(1, 1, 3), (1, 3, 1), (3, 1, 1)]
    for n in [5, 13, 17, 29, 97, 101]:
        for x, y, w in z.zagier_set(n):
            assert x * x + 4 * y * w == n and min(x, y, w) >= 1


def test_map_is_an_involution_with_one_fixed_point_for_primes():
    for p in [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 1009]:
        s = z.zagier_set(p)
        assert all(z.zagier_map(t) in s for t in s)
        assert all(z.zagier_map(z.zagier_map(t)) == t for t in s)
        k = (p - 1) // 4
        assert [t for t in s if z.zagier_map(t) == t] == [(1, 1, k)]
        assert len(s) % 2 == 1


def test_swap_fixed_points_give_two_squares():
    for p in [5, 13, 17, 29, 97, 2969]:
        report = z.audit(p)
        assert report["squares"]
        for a, b in report["squares"]:
            assert a * a + b * b == p


def test_claims_hold_exactly_for_primes_in_range():
    for n in range(5, 400, 4):
        holds = z.claims_hold(n, z.audit(n))
        if z.is_prime(n):
            assert holds, n
        else:
            assert not holds, n


def test_where_the_argument_breaks():
    # 21 = 3 * 7: two fixed points, |S| even, and 21 is not a sum of two squares.
    r21 = z.audit(21)
    assert sorted(r21["fixed"]) == [(1, 1, 5), (3, 3, 1)]
    assert r21["size"] % 2 == 0 and r21["squares"] == []
    # 9 is a square: a triple lies on the boundary x = y - z and its image leaves S.
    r9 = z.audit(9)
    assert r9["boundary"] == [(1, 2, 1)] and not r9["maps_into"]
    # 65 = 5 * 13: the argument fails, but 65 = 1^2 + 8^2 anyway.
    r65 = z.audit(65)
    assert len(r65["fixed"]) == 2 and (1, 8) in r65["squares"]


def test_boundary_detection():
    assert z.on_boundary((1, 2, 1))
    assert z.on_boundary((4, 2, 1))
    assert not z.on_boundary((1, 1, 3))
