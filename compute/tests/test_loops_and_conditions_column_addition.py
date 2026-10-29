import loops_and_conditions_column_addition as ca


def test_digits():
    assert ca.digits_ones_first(368) == [8, 6, 3]
    assert ca.digits_ones_first(0) == []
    assert ca.digits_ones_first(1000) == [0, 0, 0, 1]


def test_trace_of_368_plus_275():
    answer, steps = ca.column_add(368, 275)
    assert answer == 643
    assert steps == [(8, 5, 0, 13, 3, 1), (6, 7, 1, 14, 4, 1), (3, 2, 1, 6, 6, 0)]


def test_final_carry_and_unequal_lengths():
    assert ca.column_add(999, 1)[0] == 1000
    assert ca.column_add(5, 5)[0] == 10
    assert ca.column_add(0, 0)[0] == 0
    assert ca.column_add(12345, 678)[0] == 13023


def test_agrees_with_addition_and_carry_at_most_one():
    right, total, carry = ca.check_pairs([(a, b) for a in range(120) for b in range(120)])
    assert right and total == 19 and carry == 1
    right, total, carry = ca.check_pairs([(10 ** 9 - 1, 10 ** 9 - 1), (31415926, 27182818)])
    assert right and carry <= 1 and total <= 19
