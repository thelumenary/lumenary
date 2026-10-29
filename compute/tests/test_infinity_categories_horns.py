import pytest

import infinity_categories_horns as ih

POSET, IDEMPOTENT, Z3, ISO = ih.CATEGORIES


def test_categories_are_categories():
    """Identity and associativity laws hold in each test category."""
    for cat in ih.CATEGORIES:
        arrows = list(cat.arrows)
        for f in arrows:
            for g in arrows:
                if cat.arrows[f][1] != cat.arrows[g][0]:
                    continue
                fg = cat.compose(f, g)
                assert cat.arrows[fg] == (cat.arrows[f][0], cat.arrows[g][1])
                for h in arrows:
                    if cat.arrows[g][1] == cat.arrows[h][0]:
                        assert cat.compose(fg, h) == cat.compose(f, cat.compose(g, h))


def test_hom_sets():
    assert POSET.hom(0, 2) == [(0, 2)]
    assert POSET.hom(2, 0) == []
    assert sorted(IDEMPOTENT.hom(0, 0)) == ["1", "e"]
    assert ISO.hom(0, 1) == ["u"]


@pytest.mark.parametrize("cat", ih.CATEGORIES, ids=lambda c: c.name)
@pytest.mark.parametrize("n,k", [(2, 1), (3, 1), (3, 2)])
def test_inner_horns_fill_uniquely(cat, n, k):
    horns, fillable, most = ih.horn_census(cat, n, k)
    assert horns > 0
    assert fillable == horns
    assert most == 1


@pytest.mark.parametrize("cat", [Z3, ISO], ids=lambda c: c.name)
@pytest.mark.parametrize("n,k", [(2, 0), (2, 2), (3, 0), (3, 3)])
def test_groupoid_outer_horns_fill(cat, n, k):
    horns, fillable, most = ih.horn_census(cat, n, k)
    assert fillable == horns and most == 1


def test_poset_outer_two_horns_fail():
    # Lambda^2_0 in the poset 0 < 1 < 2: pairs x0 <= x1, x0 <= x2; fillable iff x1 <= x2.
    assert ih.horn_census(POSET, 2, 0) == (14, 10, 1)
    assert ih.horn_census(POSET, 2, 2) == (14, 10, 1)


def test_idempotent_outer_horns_fail_or_are_not_unique():
    horns, fillable, most = ih.horn_census(IDEMPOTENT, 2, 0)
    assert (horns, fillable, most) == (4, 3, 2)
    assert ih.horn_census(IDEMPOTENT, 3, 0)[:2] == (12, 8)


def test_counts_of_inner_two_horns_are_composable_pairs():
    # Lambda^2_1 horns are composable pairs of arrows.
    for cat in ih.CATEGORIES:
        pairs = sum(1 for f in cat.arrows for g in cat.arrows
                    if cat.arrows[f][1] == cat.arrows[g][0])
        assert ih.horn_census(cat, 2, 1)[0] == pairs
