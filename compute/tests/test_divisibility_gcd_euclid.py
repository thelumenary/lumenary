from math import gcd

import pytest

import divisibility_gcd_euclid as de


def test_euclid_steps_1071_462():
    assert de.euclid_steps(1071, 462) == [(1071, 2, 462, 147), (462, 3, 147, 21), (147, 7, 21, 0)]
    assert de.euclid_steps(5, 0) == []
    with pytest.raises(ValueError):
        de.euclid_steps(-1, 3)


def test_extended_gcd_bezout():
    assert de.extended_gcd(1071, 462) == (21, -3, 7)
    for a in range(0, 60):
        for b in range(0, 60):
            g, x, y = de.extended_gcd(a, b)
            assert g == gcd(a, b)
            assert a * x + b * y == g


def test_last_nonzero_remainder_is_gcd():
    for a, b in [(252, 198), (1071, 462), (89, 55), (1000, 1)]:
        steps = de.euclid_steps(a, b)
        assert steps[-1][2] == gcd(a, b)
        # remainders strictly decrease
        rs = [r for *_, r in steps]
        assert all(x > y for x, y in zip(rs, rs[1:]))


def test_fibonacci_worst_cases():
    assert [de.fibonacci(k) for k in range(10)] == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
    for k in range(2, 25):
        assert len(de.euclid_steps(de.fibonacci(k + 1), de.fibonacci(k))) == k - 1


def test_slowest_pair_and_lame_bound():
    pair, n = de.slowest_pair(100, 300)
    assert pair == (144, 89) and n == 10
    for b in range(1, 200):
        for a in range(b + 1, 2 * b + 2):
            assert len(de.euclid_steps(a, b)) <= 5 * len(str(b))
