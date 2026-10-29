import quantifiers_set_builder as qs


def test_two_descriptions_of_the_evens_agree():
    for limit in [0, 1, 2, 7, 10, 1001]:
        assert qs.evens_by_property(limit) == qs.evens_by_formula(limit)
    assert qs.evens_by_property(7) == {0, 2, 4, 6}


def test_small_squares_and_primes():
    assert qs.small_squares() == [-3, -2, -1, 0, 1, 2, 3]
    assert qs.primes_below(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert qs.primes_below(2) == []


def test_missing_numbers_are_really_missing():
    samples = [[], [0], [0, 1, 2, 3], [5, 10 ** 6, 41], list(range(0, 50, 2))]
    for nums in samples:
        n, e = qs.missing_natural(nums), qs.missing_even(nums)
        assert n not in nums and n >= 0
        assert e not in nums and e % 2 == 0
        assert all(x < n for x in nums) and all(x < e or e == 0 for x in nums)


def test_missing_values_for_specific_lists():
    assert qs.missing_natural([]) == 0
    assert qs.missing_natural([7, 3, 12]) == 13
    assert qs.missing_even([7, 3, 12]) == 26
    assert qs.missing_even([2, 4, 6, 8, 10, 12]) == 26
