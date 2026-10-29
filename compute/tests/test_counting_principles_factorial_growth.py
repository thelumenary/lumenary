import math

import counting_principles_factorial_growth as cf


def test_crossover_points():
    assert cf.first_n_where_factorial_exceeds(2) == 4
    assert cf.first_n_where_factorial_exceeds(10) == 25
    assert math.factorial(24) < 10 ** 24 < 10 ** 25 < math.factorial(25)


def test_digits_of_52_factorial():
    assert cf.digits(math.factorial(52)) == 68
    assert cf.digits(1) == 1 and cf.digits(10 ** 5) == 6


def test_stirling_underestimates_with_shrinking_error():
    errors = [cf.relative_error(n) for n in (1, 2, 5, 10, 20, 52)]
    assert all(e > 0 for e in errors)
    assert errors == sorted(errors, reverse=True)
    for n in (5, 10, 20, 52):
        assert abs(cf.relative_error(n) - 1 / (12 * n)) < 1 / (12 * n) ** 2


def test_years_to_list():
    assert abs(cf.years_to_list(cf.SECONDS_PER_YEAR, 1) - 1) < 1e-12
    assert cf.years_to_list(math.factorial(52), 1e9) > 1e50
