import random

import pytest

import whole_number_arithmetic_column_method as cm


def test_digits_round_trip():
    assert cm.digits(0) == [0]
    assert cm.digits(407) == [7, 0, 4]
    for n in [0, 5, 10, 99, 1081, 123456789]:
        assert cm.from_digits(cm.digits(n)) == n
    with pytest.raises(ValueError):
        cm.digits(-3)


def test_times_one_digit_records_carries():
    product, steps = cm.times_one_digit(47, 3)
    assert product == 141
    assert steps == [(7, 21, 1, 2), (4, 14, 4, 1)]
    assert cm.times_one_digit(999, 9)[0] == 8991
    assert cm.times_one_digit(123, 0)[0] == 0
    with pytest.raises(ValueError):
        cm.times_one_digit(5, 10)


def test_partial_products_and_area_model_for_47_times_23():
    assert cm.partial_products(47, 23) == [141, 940]
    pieces = cm.area_pieces(47, 23)
    assert pieces == [(40, 20, 800), (40, 3, 120), (7, 20, 140), (7, 3, 21)]
    assert sum(p for _, _, p in pieces) == 1081 == sum(cm.partial_products(47, 23))


def test_column_method_agrees_with_python():
    assert cm.count_mismatches([(a, b) for a in range(60) for b in range(60)]) == 0
    rng = random.Random(7)
    for _ in range(200):
        a, b = rng.randrange(10 ** 9), rng.randrange(10 ** 6)
        assert cm.column_multiply(a, b) == a * b
    # Zeros inside numbers are handled by place value.
    assert cm.column_multiply(1005, 407) == 409035


def test_forgetting_carries_breaks_the_method():
    assert cm.column_multiply(47, 3, carry_on=False) == 21
    # 12 x 3 = 36 needs no carry, so the broken method still gets it right.
    assert cm.column_multiply(12, 3, carry_on=False) == 36
    pairs = [(a, b) for a in range(100) for b in range(10)]
    assert 0 < cm.count_mismatches(pairs, carry_on=False) < len(pairs)
