import pytest

import counting_every_order as ce


def test_count_aloud_pairs_each_item_with_one_word():
    pairs = ce.count_aloud(["a", "b", "c"])
    assert pairs == [("one", "a"), ("two", "b"), ("three", "c")]
    assert [item for _, item in pairs] == ["a", "b", "c"]
    assert ce.count_aloud([]) == []
    with pytest.raises(ValueError):
        ce.count_aloud(range(len(ce.NUMBER_WORDS) + 1))


def test_last_word_is_the_number_of_items():
    for n in range(len(ce.NUMBER_WORDS) + 1):
        expected = ce.NUMBER_WORDS[n - 1] if n else "zero"
        assert ce.last_word(range(n)) == expected


def test_every_order_ends_on_the_same_word():
    tally = ce.last_words_in_every_order(ce.HERD)
    assert tally == {"five": 120}
    assert ce.last_words_in_every_order(["x", "y", "z", "w"]) == {"four": 24}
    assert ce.last_words_in_every_order([]) == {"zero": 1}


def test_counting_slips_change_the_answer():
    herd = list(ce.HERD)
    assert ce.touches(herd) == herd
    assert ce.touches(herd, skip=2) == ["Snowy", "Patch", "Star", "Pebble"]
    assert ce.last_word(ce.touches(herd, skip=2)) == "four"
    assert ce.touches(herd, twice=3).count("Star") == 2
    assert ce.last_word(ce.touches(herd, twice=3)) == "six"
    # A skip and a double touch cancel out: the right number, by luck.
    assert ce.last_word(ce.touches(herd, skip=0, twice=4)) == "five"


def test_pair_up_leaves_at_most_one_side_over():
    pairs, kids_left, cups_left = ce.pair_up(ce.CHILDREN, ce.CUPS)
    assert len(pairs) == 4
    assert kids_left == ["Tomás"] and cups_left == []
    pairs, left_a, left_b = ce.pair_up("abc", "xyz")
    assert len(pairs) == 3 and left_a == [] and left_b == []
    _, left_a, left_b = ce.pair_up([], [1, 2])
    assert left_a == [] and left_b == [1, 2]


def test_pairing_agrees_with_counting():
    for m in range(6):
        for n in range(6):
            _, left_a, left_b = ce.pair_up(range(m), range(n))
            assert (not left_a and not left_b) == (m == n)
            assert len(left_a) == max(m - n, 0)
            assert len(left_b) == max(n - m, 0)
