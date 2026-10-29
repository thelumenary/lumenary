import pytest

import factors_primes_divisibility_tests as fdt


def test_digits_and_sums():
    assert fdt.digits(0) == [0]
    assert fdt.digits(572) == [2, 7, 5]
    assert fdt.digit_sum(572) == 14
    assert fdt.digit_sum(999_999) == 54
    assert fdt.alternating_sum(121) == 1 - 2 + 1
    assert fdt.alternating_sum(918_082) == 2 - 8 + 0 - 8 + 1 - 9
    with pytest.raises(ValueError):
        fdt.digits(-5)


def test_real_tests_never_fail():
    real = [rule for rule in fdt.RULES if "guess" not in rule[0]]
    assert len(real) == 7
    for _, d, test in real:
        assert fdt.first_failure(test, d, limit=20_000) is None


def test_false_shortcuts_have_small_counterexamples():
    rules = {name: (d, test) for name, d, test in fdt.RULES}
    d, test = rules["digit sum for 7 (a guess)"]
    assert fdt.first_failure(test, d) == 14
    d, test = rules["last digit for 4 (a guess)"]
    assert fdt.first_failure(test, d) == 10


def test_digit_sum_keeps_remainder_mod_9_and_3():
    for n in range(0, 50_000, 7):
        assert n % 9 == fdt.digit_sum(n) % 9
        assert n % 3 == fdt.digit_sum(n) % 3
        assert n % 11 == fdt.alternating_sum(n) % 11
