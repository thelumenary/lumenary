from itertools import product

import pytest

import cantor_diagonal as cd

SEQS = [rule for _, rule in cd.SEQUENCES]


def test_listed_sequences_first_digits():
    expected = {
        "all zeros": "000000000000",
        "all ones": "111111111111",
        "alternating": "010101010101",
        "1 at squares": "110010000100",
        "1 at primes": "001101010001",
        "Thue-Morse": "011010011001",
        "1 at multiples of 3": "100100100100",
        "binary digits of sqrt 2": "011010100000",
    }
    for name, rule in cd.SEQUENCES:
        assert "".join(map(str, cd.prefix(rule, 12))) == expected[name], name


def test_sqrt2_digits_are_correct():
    # sqrt(2) = 1.0110101000001001111001100110011111110011101111001100... in binary
    assert "".join(str(cd._sqrt2_digit(n)) for n in range(40)) == "0110101000001001111001100110011111110011"


def test_prefix_boundaries():
    assert cd.prefix(SEQS[1], 0) == []
    assert cd.prefix(SEQS[2], 3) == [0, 1, 0]


def test_diagonal_flip_differs_from_every_listed_sequence():
    d = cd.diagonal_flip(SEQS)
    assert [d(n) for n in range(len(SEQS))] == [1, 0, 1, 1, 1, 1, 0, 1]
    assert cd.differs_from_every_row(SEQS, d)
    for i, s in enumerate(SEQS):
        assert d(i) != s(i)
        assert cd.first_difference(d, s, len(SEQS)) is not None


def test_diagonal_is_undefined_beyond_a_finite_list():
    d = cd.diagonal_flip(SEQS)
    with pytest.raises(IndexError):
        d(len(SEQS))
    with pytest.raises(IndexError):
        d(-1)


@pytest.mark.parametrize("order", [list(range(8)), list(reversed(range(8))), [3, 1, 4, 0, 5, 2, 6, 7]])
def test_any_order_and_any_sublist_is_beaten(order):
    seqs = [SEQS[i] for i in order]
    for length in range(len(seqs) + 1):
        assert cd.differs_from_every_row(seqs[:length], cd.diagonal_flip(seqs[:length]))


def test_empty_list():
    d = cd.diagonal_flip([])
    assert cd.differs_from_every_row([], d)


def test_first_difference():
    assert cd.first_difference(SEQS[0], SEQS[1], 5) == 0
    assert cd.first_difference(SEQS[0], SEQS[0], 5) is None
    assert cd.first_difference(SEQS[0], SEQS[4], 10) == 2


def test_diagonal_flip_rows_square_and_rectangular():
    assert cd.diagonal_flip_rows([[0, 1], [1, 1]]) == [1, 0]
    assert cd.diagonal_flip_rows([[0, 0, 0]]) == [1]
    assert cd.diagonal_flip_rows([]) == []


def test_diagonal_flip_rows_needs_a_position_per_row():
    rows = [list(bits) for bits in product((0, 1), repeat=3)]
    with pytest.raises(ValueError):
        cd.diagonal_flip_rows(rows)


def test_finite_lists_of_finite_strings_can_be_complete():
    rows = [list(bits) for bits in product((0, 1), repeat=3)]
    flipped = cd.diagonal_flip_rows(rows[:3])
    assert flipped in rows  # the "new" string is just further down the complete list
    assert rows.index(flipped) == 7


def test_show_row():
    assert cd.show_row([0, 1, 0], mark=1) == " 0 [1] 0 "
    assert cd.show_row([1]) == " 1 "
