import pytest

import recurrences_generating_functions_binet as rb


def test_fib_list_values():
    assert rb.fib_list(0) == []
    assert rb.fib_list(11) == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
    f = rb.fib_list(100)
    assert all(f[n + 2] == f[n + 1] + f[n] for n in range(98))


def test_series_divide_geometric_and_fibonacci():
    # 1/(1 - x) = 1 + x + x^2 + ...
    assert rb.series_divide([1], [1, -1], 6) == [1] * 6
    # x/(1 - x - x^2) is the Fibonacci generating function
    assert rb.series_divide([0, 1], [1, -1, -1], 50) == rb.fib_list(50)
    # (1 + x)^2 / 1 is a polynomial: the series stops
    assert rb.series_divide([1, 2, 1], [1], 5) == [1, 2, 1, 0, 0]
    with pytest.raises(ValueError):
        rb.series_divide([1], [2, 1], 3)


def test_fib_matrix_matches_and_is_fast():
    f = rb.fib_list(200)
    assert all(rb.fib_matrix(n)[0] == f[n] for n in range(200))
    value, mults = rb.fib_matrix(1000)
    assert len(str(value)) == 209
    assert mults <= 2 * 10  # about 2 log2(n) products
    with pytest.raises(ValueError):
        rb.fib_matrix(-1)


def test_binet_float_correct_then_fails():
    f = rb.fib_list(80)
    assert all(rb.binet_float(n) == f[n] for n in range(71))
    assert rb.first_binet_failure(200) == 71
    assert rb.first_binet_failure(50) is None


def test_cassini():
    assert rb.cassini_holds(300)
    f = rb.fib_list(10)
    assert f[6] * f[4] - f[5] ** 2 == -1  # n = 5: (-1)^5
    assert f[5] * f[3] - f[4] ** 2 == 1  # n = 4: (-1)^4
