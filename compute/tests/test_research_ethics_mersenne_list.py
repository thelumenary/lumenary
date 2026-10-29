import research_ethics_mersenne_list as m


def test_lucas_lehmer_small_cases():
    assert [p for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] if m.lucas_lehmer(p)] == [
        2, 3, 5, 7, 13, 17, 19, 31]


def test_lucas_lehmer_agrees_with_trial_division():
    for p in [2, 3, 5, 7, 11, 13]:
        assert m.lucas_lehmer(p) == m.is_prime(2 ** p - 1)


def test_mersenne_exponents_up_to_257():
    assert m.mersenne_exponents(257) == [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127]


def test_comparison_with_mersennes_claim():
    wrong, missing = m.compare(m.MERSENNE_CLAIM, m.mersenne_exponents(257))
    assert wrong == [67, 257]
    assert missing == [61, 89, 107]
    assert m.compare([1, 2], [2, 3]) == ([1], [3])


def test_other_corrections():
    assert 193707721 * 761838257287 == 2 ** 67 - 1
    assert (2 ** 32 + 1) % 641 == 0
    assert 27 ** 5 + 84 ** 5 + 110 ** 5 + 133 ** 5 == 144 ** 5
    assert not m.lucas_lehmer(67) and not m.lucas_lehmer(257)
