import pytest

import set_identities as si

U = si.UNIVERSE


@pytest.mark.parametrize("n", [0, 1, 2, 3, 4, 5])
def test_all_subsets_has_two_to_the_n_distinct_members(n):
    universe = frozenset(range(n))
    subsets = si.all_subsets(universe)
    assert len(subsets) == 2 ** n
    assert len(set(subsets)) == 2 ** n
    assert subsets[0] == frozenset() and subsets[-1] == universe
    assert all(s <= universe for s in subsets)
    assert [len(s) for s in subsets] == sorted(len(s) for s in subsets)


def test_complement():
    assert si.complement(frozenset({1, 3}), U) == frozenset({2, 4})
    assert si.complement(frozenset(), U) == U
    assert si.complement(U, U) == frozenset()


def test_bitmask_round_trip_for_every_subset():
    for s in si.all_subsets(U):
        assert si.from_bitmask(si.to_bitmask(s, U), U) == s
    assert sorted(si.to_bitmask(s, U) for s in si.all_subsets(U)) == list(range(16))


def test_bitmask_examples():
    assert si.to_bitmask({1, 3}, U) == 0b0101
    assert si.to_bitmask(set(), U) == 0
    assert si.to_bitmask(U, U) == 0b1111


def test_bitmask_rejects_bad_input():
    with pytest.raises(ValueError):
        si.to_bitmask({5}, U)
    with pytest.raises(ValueError):
        si.from_bitmask(16, U)
    with pytest.raises(ValueError):
        si.from_bitmask(-1, U)


def test_bit_operations_agree():
    assert si.bit_operations_agree(U) == 256
    assert si.bit_operations_agree(frozenset()) == 1


@pytest.mark.parametrize("name,arity,lhs,rhs", si.IDENTITIES, ids=[i[0] for i in si.IDENTITIES])
@pytest.mark.parametrize("n", [0, 1, 2, 4])
def test_true_identities_have_no_counterexamples(name, arity, lhs, rhs, n):
    cases, failures = si.check_identity(lhs, rhs, frozenset(range(n)), arity)
    assert cases == (2 ** n) ** arity
    assert failures == []
    assert si.smallest_counterexample(lhs, rhs, frozenset(range(n)), arity) is None


def test_non_identity_fails_exactly_when_a_and_c_meet():
    _, arity, lhs, rhs = si.NON_IDENTITY
    cases, failures = si.check_identity(lhs, rhs, U, arity)
    assert cases == 4096
    # The two sides differ exactly when A and C share an element: 4096 - 6**4 cases.
    assert len(failures) == 4096 - 6 ** 4 == 2800
    assert all(A & C for A, B, C in failures)


def test_smallest_counterexample_is_minimal_and_genuine():
    _, arity, lhs, rhs = si.NON_IDENTITY
    A, B, C = si.smallest_counterexample(lhs, rhs, U, arity)
    assert (A, B, C) == (frozenset({1}), frozenset(), frozenset({1}))
    assert lhs(U, A, B, C) != rhs(U, A, B, C)


def test_non_identity_holds_on_the_empty_universe():
    # With no elements there is only one subset, so no counterexample can exist.
    _, arity, lhs, rhs = si.NON_IDENTITY
    assert si.smallest_counterexample(lhs, rhs, frozenset(), arity) is None


def test_fmt():
    assert si.fmt(frozenset()) == "∅"
    assert si.fmt({3, 1}) == "{1, 3}"
