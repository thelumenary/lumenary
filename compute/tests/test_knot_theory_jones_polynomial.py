import pytest

import knot_theory_jones_polynomial as kj

TREFOIL = kj.KNOTS["3_1 (right trefoil)"]
MIRROR = kj.KNOTS["3_1 mirror (left)"]
FIG8 = kj.KNOTS["4_1 (figure eight)"]


def test_pd_codes_are_well_formed():
    for pd in kj.KNOTS.values():
        labels = [x for crossing in pd for x in crossing]
        assert sorted(set(labels)) == list(range(1, 2 * len(pd) + 1))
        assert all(labels.count(x) == 2 for x in set(labels))


def test_trefoil_bracket_and_writhe():
    assert kj.bracket(TREFOIL) == {-7: 1, -3: -1, 5: -1}
    assert kj.writhe(TREFOIL) == 3
    assert kj.writhe(MIRROR) == -3
    # mirror image: A -> 1/A
    assert kj.bracket(MIRROR) == {-e: c for e, c in kj.bracket(TREFOIL).items()}


def test_known_jones_polynomials():
    assert kj.jones(TREFOIL) == {4: -1, 3: 1, 1: 1}
    assert kj.jones(MIRROR) == {-1: 1, -3: 1, -4: -1}
    assert kj.jones(FIG8) == {2: 1, 1: -1, 0: 1, -1: -1, -2: 1}
    assert kj.jones(kj.KNOTS["6_1"]) == {2: 1, 1: -1, 0: 2, -1: -2, -2: 1,
                                         -3: -1, -4: 1}


def test_v_at_one_is_one_for_knots():
    for pd in kj.KNOTS.values():
        assert sum(kj.jones(pd).values()) == 1


def test_kinks_change_bracket_by_minus_a_cubed_but_not_jones():
    for pd in (TREFOIL, FIG8):
        b = kj.bracket(pd)
        assert kj.bracket(kj.add_kink(pd, True)) == kj.multiply(b, {3: -1})
        assert kj.bracket(kj.add_kink(pd, False)) == kj.multiply(b, {-3: -1})
        assert kj.writhe(kj.add_kink(pd, True)) == kj.writhe(pd) + 1
        assert kj.writhe(kj.add_kink(pd, False)) == kj.writhe(pd) - 1
        assert kj.jones(kj.add_kink(pd)) == kj.jones(pd)


def test_loops_counts():
    assert kj.loops(TREFOIL, "AAA") == 2
    assert kj.loops(TREFOIL, "BBB") == 3
    assert kj.bracket([]) == {0: 1}


def test_crossing_sign_needs_orientable_input():
    with pytest.raises(ValueError):
        kj.crossing_sign((1, 1, 2, 4), 6)


def test_show_formatting():
    assert kj.show({4: -1, 3: 1, 1: 1}) == "-t^4 + t^3 + t"
    assert kj.show({0: 2, -1: -2}) == "2 - 2t^-1"
    assert kj.show({5: -1, -3: -1, -7: 1}, "A") == "-A^5 - A^-3 + A^-7"
