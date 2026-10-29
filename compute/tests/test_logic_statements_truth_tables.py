import logic_statements_truth_tables as lt


def test_four_rows():
    assert len(lt.ROWS) == 4
    assert set(lt.ROWS) == {(True, True), (True, False), (False, True), (False, False)}


def test_inclusive_or_is_true_when_both_true():
    assert lt.inclusive_or(True, True) is True
    assert lt.inclusive_or(True, False) and lt.inclusive_or(False, True)
    assert lt.inclusive_or(False, False) is False


def test_exclusive_or_differs_only_when_both_true():
    assert lt.exclusive_or(True, True) is False
    assert lt.rows_that_differ(lt.inclusive_or, lt.exclusive_or) == [(True, True)]


def test_de_morgan_and_double_negation():
    assert lt.same_in_every_row(lambda p, q: not (p and q), lambda p, q: (not p) or (not q))
    assert lt.same_in_every_row(lambda p, q: not (p or q), lambda p, q: (not p) and (not q))
    assert lt.same_in_every_row(lambda p, q: not (not p), lambda p, q: p)


def test_a_wrong_law_is_caught():
    # "not (p and q)" is NOT the same as "(not p) and (not q)": they differ in two rows.
    wrong = lt.rows_that_differ(lambda p, q: not (p and q), lambda p, q: (not p) and (not q))
    assert wrong == [(True, False), (False, True)]
    assert not lt.same_in_every_row(lambda p, q: p and q, lambda p, q: p or q)


def test_word():
    assert lt.word(True) == "T" and lt.word(False) == "F"
