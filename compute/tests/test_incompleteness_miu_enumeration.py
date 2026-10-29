import incompleteness_miu_enumeration as miu


def test_successors_apply_each_rule():
    assert miu.successors("MI") == {"MIU", "MII"}
    assert "MUI" in miu.successors("MIIII") and "MIU" in miu.successors("MIIII")
    assert "MI" in miu.successors("MUUI")
    # Rule 1 needs a final I; rule 3 needs III; rule 4 needs UU.
    assert miu.successors("MU") == {"MUU"}


def test_rules_preserve_the_invariant():
    for s in ["MI", "MII", "MIIII", "MUIUI", "MIIIIIIIU"]:
        if miu.invariant(s) != 0:
            assert all(miu.invariant(t) != 0 for t in miu.successors(s))


def test_enumeration_is_monotone_in_the_bound():
    small, large = miu.theorems(8), miu.theorems(12)
    assert small <= large
    assert "MI" in small and "MU" not in large
    assert all(len(s) <= 12 for s in large)


def test_known_small_theorems():
    found = miu.theorems(16)
    for s in ["MI", "MII", "MIIII", "MUI", "MIU", "MIIU"]:
        assert s in found
    assert all(miu.invariant(s) != 0 for s in found)


def test_characterisation_on_short_strings():
    found = miu.theorems(16)
    assert miu.characterisation_failures(found, 7) == []
    # With too small a search bound some theorems are missed: the bound matters.
    assert miu.characterisation_failures(miu.theorems(8), 7) != []
