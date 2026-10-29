import large_cardinals_laver_tables as lt


def test_small_tables():
    assert lt.laver_table(0) == {1: [1]}
    assert lt.laver_table(1) == {2: [1, 2], 1: [2, 2]}
    a2 = lt.laver_table(2)
    assert [a2[p] for p in range(1, 5)] == [[2, 4, 2, 4], [3, 4, 3, 4], [4, 4, 4, 4], [1, 2, 3, 4]]


def test_defining_properties():
    for n in range(6):
        rows = lt.laver_table(n)
        size = 2 ** n
        assert all(lt.star(rows, p, 1) == p % size + 1 for p in range(1, size + 1))
        assert lt.is_left_distributive(rows)


def test_distributivity_check_detects_failure():
    # Ordinary addition mod 4 (on 1..4) is not left self-distributive.
    rows = {p: [(p + q - 1) % 4 + 1 for q in range(1, 5)] for p in range(1, 5)}
    assert not lt.is_left_distributive(rows)


def test_rows_increase_within_a_period():
    rows = lt.laver_table(6)
    for p in range(1, 64):
        row = rows[p]
        d = lt.period(row)
        assert all(x < y for x, y in zip(row[:d], row[1:d]))
        assert row[d - 1] == 64


def test_period_of_first_row():
    assert [lt.period(lt.laver_table(n)[1]) for n in range(10)] == [1, 1, 2, 4, 4, 8, 8, 8, 8, 16]
    assert lt.period([1, 2, 1, 2]) == 2
    assert lt.period([1, 2, 3]) == 3
