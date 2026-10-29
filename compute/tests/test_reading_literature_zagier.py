import reading_literature_zagier as rz


def test_zagier_set_small_cases():
    assert sorted(rz.zagier_set(5)) == [(1, 1, 1)]
    assert sorted(rz.zagier_set(13)) == [(1, 1, 3), (1, 3, 1), (3, 1, 1)]
    assert rz.zagier_set(19) == []            # x^2 + 4yz is 1 mod 4
    for t in rz.zagier_set(97):
        x, y, z = t
        assert x * x + 4 * y * z == 97 and min(t) >= 1


def test_map_is_an_involution_with_one_fixed_point_for_primes():
    for p in (5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 1009):
        a = rz.analyse(p)
        assert a["involution"] and a["boundary"] == 0
        assert a["fixed"] == [(1, 1, (p - 1) // 4)]
        assert a["size"] % 2 == 1
        u, v = a["squares"][0]
        assert u * u + v * v == p


def test_check_primes_below_3000():
    count, bad = rz.check_primes(3000)
    assert bad == []
    assert count == 211          # primes p = 1 (mod 4) below 3000


def test_where_the_hypotheses_are_used():
    # composites: several fixed points, conclusion may fail
    a21 = rz.analyse(21)
    assert a21["fixed"] == [(1, 1, 5), (3, 3, 1)] and a21["squares"] == []
    a45 = rz.analyse(45)
    assert len(a45["fixed"]) == 3 and a45["squares"] == [(3, 6)]
    # squares: boundary points, so the map is not an involution of S
    a9 = rz.analyse(9)
    assert a9["boundary"] == 1 and not a9["involution"]


def test_zagier_map_cases():
    assert rz.zagier_map((1, 3, 1)) == (3, 1, 1)      # first case
    assert rz.zagier_map((3, 1, 1)) == (1, 3, 1)      # third case
    assert rz.zagier_map((1, 1, 3)) == (1, 1, 3)      # second case, fixed
    assert rz.zagier_map((1, 2, 1)) is None           # boundary x = y - z
    assert rz.zagier_map((2, 1, 5)) is None           # boundary x = 2y
