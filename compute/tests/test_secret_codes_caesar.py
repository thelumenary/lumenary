import secret_codes_caesar as sc


def test_shift_letter_wraps_round():
    assert sc.shift_letter("A", 3) == "D"
    assert sc.shift_letter("X", 3) == "A"
    assert sc.shift_letter("Z", 3) == "C"
    assert sc.shift_letter("M", 26) == "M"


def test_caesar_examples():
    assert sc.caesar("MEET AT NOON", 3) == "PHHW DW QRRQ"
    assert sc.caesar("ZEBRA", 3) == "CHEUD"
    assert sc.caesar("PHHW DW QRRQ", 23) == "MEET AT NOON"
    assert sc.caesar("HELLO, WORLD!", 0) == "HELLO, WORLD!"


def test_shift_by_26_minus_k_undoes_k():
    message = "THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG"
    for k in range(27):
        assert sc.caesar(sc.caesar(message, k), 26 - k) == message


def test_only_26_different_shifts():
    results = {sc.caesar("ABCDEFGHIJKLMNOPQRSTUVWXYZ", k) for k in range(100)}
    assert len(results) == 26
    assert sc.caesar("HELLO", 5 + 26) == sc.caesar("HELLO", 5)


def test_breaking_the_secret():
    k = sc.best_shift(sc.SECRET)
    assert k == 15
    assert sc.caesar(sc.SECRET, k) == "THE TREASURE IS UNDER THE MANGO TREE"
    assert sc.english_score("THE TREASURE IS UNDER THE MANGO TREE") < sc.english_score(sc.SECRET)
