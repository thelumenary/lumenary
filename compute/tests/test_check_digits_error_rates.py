import itertools

import check_digits_error_rates as cd


def test_known_codes():
    assert cd.isbn10_valid([3, 1, 6, 1, 4, 8, 4, 1, 0, 10])
    assert cd.isbn10_check([3, 1, 6, 1, 4, 8, 4, 1, 0]) == 10
    assert cd.isbn13_valid([9, 7, 8, 3, 1, 6, 1, 4, 8, 4, 1, 0, 0])
    assert cd.isbn13_check([9, 7, 8, 3, 1, 6, 1, 4, 8, 4, 1, 0]) == 0
    assert cd.luhn_valid([7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3])
    assert cd.luhn_check([7, 9, 9, 2, 7, 3, 9, 8, 7, 1]) == 3
    assert not cd.isbn10_valid([3, 6, 1, 1, 4, 8, 4, 1, 0, 10])
    # The ISBN-13 blind spot: swapping neighbours 1 and 6 (they differ by 5).
    assert cd.isbn13_valid([9, 7, 8, 3, 6, 1, 1, 4, 8, 4, 1, 0, 0])


def test_generated_codes_are_valid_and_deterministic():
    for scheme, valid in cd.VALID.items():
        codes = cd.make_codes(scheme, 50)
        assert len(codes) == 50 and all(valid(c) for c in codes)
        assert codes == cd.make_codes(scheme, 50)


def test_error_counts():
    code = [3, 1, 6, 1, 4, 8, 4, 1, 0, 10]
    assert len(cd.errors(code, "single", isbn10=True)) == 9 * 9 + 10
    swaps = cd.errors(code, "neighbour swap")
    assert len(swaps) == sum(code[i] != code[i + 1] for i in range(9))
    assert swaps[0] == [1, 3, 6, 1, 4, 8, 4, 1, 0, 10]
    jumps = cd.errors(code, "jump swap")
    assert jumps[0] == [6, 1, 3, 1, 4, 8, 4, 1, 0, 10]


def test_isbn10_catches_every_single_error_and_swap():
    codes = cd.make_codes("ISBN-10", 100, seed=7)
    for kind in ("single", "neighbour swap", "jump swap"):
        caught, total = cd.detection("ISBN-10", kind, codes)
        assert caught == total > 0


def test_isbn13_and_luhn_swap_blind_spots_exactly():
    for a, b in itertools.product(range(10), repeat=2):
        if a == b:
            continue
        base13 = [0] * 11 + [a, b]
        base13[0] = (-(3 * a + b)) % 10  # positions 12, 13 have weights 3, 1
        assert cd.isbn13_valid(base13)
        swapped = base13[:11] + [b, a]
        assert cd.isbn13_valid(swapped) == (abs(a - b) == 5)
        luhn = [a, b]
        luhn_code = luhn + [cd.luhn_check(luhn)]
        swapped_luhn = [b, a] + luhn_code[2:]
        assert cd.luhn_valid(swapped_luhn) == ({a, b} == {0, 9})


def test_digit_sum_misses_all_swaps():
    codes = cd.make_codes("digit sum", 60)
    caught, total = cd.detection("digit sum", "neighbour swap", codes)
    assert caught == 0 and total > 0
    caught, total = cd.detection("digit sum", "single", codes)
    assert caught == total


def test_luhn_double_is_a_shuffle():
    assert sorted(cd.luhn_double(d) for d in range(10)) == list(range(10))
    assert [cd.luhn_double(d) for d in range(10)] == [0, 2, 4, 6, 8, 1, 3, 5, 7, 9]
