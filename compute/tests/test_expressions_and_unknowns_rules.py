import expressions_and_unknowns_rules as er


def test_fits():
    assert er.fits(lambda n: 3 * n + 1, er.TABLE)
    assert not er.fits(lambda n: 3 * n + 2, er.TABLE)
    assert er.fits(lambda n: 99, [])  # no rows: every rule fits


def test_one_row_fits_many_rules():
    assert er.linear_rules_that_fit(er.TABLE[:1]) == [(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)]


def test_two_rows_pin_down_the_linear_rule():
    for k in range(2, 5):
        assert er.linear_rules_that_fit(er.TABLE[:k]) == [(3, 1)]
    assert er.linear_rules_that_fit([(1, 1), (2, 4), (3, 9)]) == []  # squares: no such rule


def test_another_kind_of_rule():
    assert er.fits(er.square_plus_three, er.TABLE[:2])
    assert not er.fits(er.square_plus_three, er.TABLE[:3])


def test_undo_three_n_plus_one():
    for n in range(0, 200):
        assert er.undo_three_n_plus_one(3 * n + 1) == n
    assert er.undo_three_n_plus_one(24) is None
    assert er.undo_three_n_plus_one(0) is None
