from decimal import Decimal

import estimation_halfway_rules as ehr


def test_rules_on_examples():
    assert [ehr.half_up(n) for n in (24, 25, 26, 35, 999)] == [20, 30, 30, 40, 1000]
    assert [ehr.half_even(n) for n in (24, 25, 26, 35, 45, 65)] == [20, 20, 30, 40, 40, 60]
    assert [ehr.always_down(n) for n in (24, 29, 30)] == [20, 20, 30]


def test_half_up_and_half_even_differ_only_on_some_fives():
    for n in range(2000):
        if n % 10 != 5:
            assert ehr.half_up(n) == ehr.half_even(n)
    differ = [n for n in range(100) if ehr.half_up(n) != ehr.half_even(n)]
    assert differ == [5, 25, 45, 65, 85]


def test_average_errors_are_exact():
    numbers = range(10_000)
    assert ehr.average_error(ehr.half_up, numbers) == Decimal("0.5")
    assert ehr.average_error(ehr.half_even, numbers) == 0
    assert ehr.average_error(ehr.always_down, numbers) == Decimal("-4.5")


def test_python_round_is_half_even_on_integers():
    for n in range(0, 5000, 5):
        assert round(n, -1) == ehr.half_even(n)
    assert round(2.5) == 2 and round(3.5) == 4
    assert Decimal(2.675) < Decimal("2.675")
