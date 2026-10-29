import pytest

import data_and_tallies_survey as ds


def test_class_tallies_match_the_lesson():
    counts = ds.tally(ds.ANSWERS)
    assert counts == {"walk": 9, "bus": 7, "bike": 5, "car": 3}
    assert list(counts) == list(ds.CATEGORIES)
    assert sum(counts.values()) == len(ds.ANSWERS) == 24


def test_tally_rejects_answers_outside_the_categories():
    assert ds.tally([]) == {"walk": 0, "bus": 0, "bike": 0, "car": 0}
    with pytest.raises(ValueError):
        ds.tally(["walk", "boat"])


def test_tally_marks_group_in_fives_and_read_back():
    assert ds.tally_marks(0) == ""
    assert ds.tally_marks(3) == "|||"
    assert ds.tally_marks(5) == ds.GATE
    assert ds.tally_marks(9) == ds.GATE + " ||||"
    assert ds.tally_marks(10) == ds.GATE + " " + ds.GATE
    for n in range(60):
        assert ds.marks_to_number(ds.tally_marks(n)) == n
    with pytest.raises(ValueError):
        ds.tally_marks(-1)


def test_picture_rows_and_misleading_lengths():
    assert ds.picture_row(0) == ""
    assert ds.picture_row(3) == "o o o"
    assert len(ds.picture_row(5)) == 9
    wide = ds.picture_row(3, "[car]")
    assert len(wide) == 17 > len(ds.picture_row(5))
    # With equal pictures, a longer row always means a bigger count.
    for m in range(12):
        for n in range(12):
            assert (len(ds.picture_row(m)) > len(ds.picture_row(n))) == (m > n)


def test_most_and_fewest_handle_ties():
    assert ds.most_and_fewest(ds.tally(ds.ANSWERS)) == (["walk"], ["car"])
    assert ds.most_and_fewest({"a": 2, "b": 2, "c": 1}) == (["a", "b"], ["c"])


def test_every_survey_adds_up():
    assert ds.every_survey_adds_up(0) == (1, True)
    assert ds.every_survey_adds_up(3) == (64, True)
    assert ds.every_survey_adds_up(6) == (4096, True)
    assert ds.every_survey_adds_up(2, ("yes", "no")) == (4, True)


def test_multiple_answers_overcount():
    totals = ds.multi_choice_totals(ds.LIKES, ("mango", "banana", "papaya"))
    assert totals == {"mango": 3, "banana": 1, "papaya": 2}
    assert sum(totals.values()) == 6 > len(ds.LIKES)
    single = [("mango",), ("banana",), ("papaya",)]
    assert sum(ds.multi_choice_totals(single, ("mango", "banana", "papaya")).values()) == 3
