import large_cardinals_hereditarily_finite as hf


def test_members_and_display():
    assert hf.members(0) == []
    assert hf.members(11) == [0, 1, 3]
    assert hf.show(3) == "{{}, {{}}}"


def test_ranks_and_stages():
    assert [hf.rank(n) for n in range(5)] == [0, 1, 2, 2, 3]
    assert [hf.size_of_v(k) for k in range(6)] == [0, 1, 2, 4, 16, 65536]
    for k in range(5):
        size = hf.size_of_v(k)
        assert all(hf.rank(n) < k for n in range(size))
        assert hf.rank(size) == k


def test_set_operations():
    assert hf.pair(0, 1) == 3 and hf.pair(2, 2) == 4
    assert hf.union(hf.pair(3, 4)) == 3 | 4
    assert hf.power_set(0) == 1  # P(empty) = {empty}
    assert hf.power_set(1) == 3  # P({0}) = {0, {0}}
    assert hf.power_set(15) == 2 ** 16 - 1  # P(V_3) = V_4


def test_ranks_of_operations():
    for a in range(20):
        for b in range(20):
            assert hf.rank(hf.pair(a, b)) == max(hf.rank(a), hf.rank(b)) + 1
        assert hf.rank(hf.union(a)) <= hf.rank(a)
        if a < 64:
            assert hf.rank(hf.power_set(a)) == hf.rank(a) + 1


def test_digit_count():
    assert hf.decimal_digits_of_power_of_two(10) == 4
    assert hf.decimal_digits_of_power_of_two(0) == 1
    assert hf.decimal_digits_of_power_of_two(65536) == 19729
