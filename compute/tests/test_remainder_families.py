import pytest

import remainder_families as rf


@pytest.mark.parametrize("n,k,r", [(7, 3, 1), (-7, 3, 2), (0, 5, 0), (-12, 4, 0), (12, 1, 0), (-1, 12, 11)])
def test_residue_is_always_in_range(n, k, r):
    assert rf.residue(n, k) == r
    assert 0 <= rf.residue(n, k) < k
    assert (n - rf.residue(n, k)) % k == 0


def test_residue_rejects_bad_modulus():
    with pytest.raises(ValueError):
        rf.residue(5, 0)


def test_residue_classes_mod_3():
    classes = rf.residue_classes(rf.NUMBERS, 3)
    assert list(classes) == [0, 1, 2]
    assert classes[0] == [-12, -9, -6, -3, 0, 3, 6, 9, 12]
    assert classes[2][:2] == [-10, -7]


def test_residue_classes_include_empty_families():
    classes = rf.residue_classes([0, 5], 5)
    assert classes == {0: [0, 5], 1: [], 2: [], 3: [], 4: []}


@pytest.mark.parametrize("k", range(1, 30))
def test_classes_partition_the_range(k):
    assert rf.is_partition(rf.residue_classes(rf.NUMBERS, k), rf.NUMBERS)


def test_is_partition_detects_overlap_and_gaps():
    assert not rf.is_partition({0: [1, 2], 1: [2]}, [1, 2])
    assert not rf.is_partition({0: [1]}, [1, 2])
    assert rf.is_partition({}, [])


@pytest.mark.parametrize("k", range(1, 13))
@pytest.mark.parametrize("op", [rf.add, rf.mul], ids=["add", "mul"])
def test_addition_and_multiplication_respect_classes(op, k):
    cases, bad = rf.depends_only_on_classes(op, rf.NUMBERS, k)
    assert cases == 25 * 25
    assert bad is None


def test_subtraction_respects_classes_too():
    assert rf.depends_only_on_classes(lambda a, b: a - b, rf.NUMBERS, 5)[1] is None


def test_power_in_exponent_does_not_respect_classes():
    _, bad = rf.depends_only_on_classes(rf.power, [2], 3, second=range(0, 7))
    (a1, b1), (a2, b2) = bad
    assert (a1, b1, a2, b2) == (2, 0, 2, 3)
    assert rf.residue(b1, 3) == rf.residue(b2, 3)
    assert rf.residue(a1 ** b1, 3) != rf.residue(a2 ** b2, 3)


def test_power_with_class_mod_2_happens_to_work_for_base_2_from_exponent_1():
    # 2^b mod 2 is 0 for every b >= 1: no counterexample there, a reminder that
    # one failed search for a counterexample is not a proof either way.
    assert rf.depends_only_on_classes(rf.power, [2], 2, second=range(1, 7))[1] is None


def test_class_table_mod_3():
    assert rf.class_table(rf.add, 3) == [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
    assert rf.class_table(rf.mul, 3) == [[0, 0, 0], [0, 1, 2], [0, 2, 1]]
