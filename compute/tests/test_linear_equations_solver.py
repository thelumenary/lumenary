from fractions import Fraction as F

import linear_equations_solver as le


def test_solve_linear_three_outcomes():
    assert le.solve_linear(3, 1, 1, 9) == ("one", F(4))
    assert le.solve_linear(2, 6, 2, 5) == ("none", None)
    assert le.solve_linear(4, -6, 4, -6) == ("all", None)
    # fractional answers stay exact
    assert le.solve_linear(2, 0, 0, 7) == ("one", F(7, 2))


def test_lesson_equations_check_by_substitution():
    expected = {
        "3x + 1 = x + 9": F(4),
        "500 - 20t = 100 + 30t": F(8),
        "x/3 + 1/2 = (x - 1)/4": F(-9),
        "5 - 2x = 11": F(-3),
    }
    for text, a, b, c, d in le.LESSON_EQUATIONS:
        kind, x = le.solve_linear(a, b, c, d)
        if text in expected:
            assert kind == "one" and x == expected[text]
            assert le.satisfies(a, b, c, d, x)
            assert not le.satisfies(a, b, c, d, x + 1)


def test_never_exactly_two_solutions():
    counts = le.solution_counts(range(-3, 4), range(-5, 6))
    assert sum(counts.values()) == 7 ** 4
    assert set(counts) <= {0, 1, 11}
    # every equation with a = c and b = d is solved by all values
    assert counts[11] == 7 * 7


def test_solution_counts_small_case():
    # coefficients in {0, 1}: 16 equations; a = c, b = d gives 4 "all" equations
    counts = le.solution_counts([0, 1], [0, 1, 2])
    assert counts[3] == 4
    assert sum(counts.values()) == 16


def test_flips_always_reverse_and_are_deterministic():
    assert le.flip_trials(2000) == 2000
    assert le.flip_trials(500, seed=7) == 500


def test_inequality_table():
    true_set, right, wrong = le.inequality_table(range(-8, 3))
    assert true_set == right == list(range(-4, 3))
    assert wrong == list(range(-8, -3))
    assert set(true_set) & set(wrong) == {-4}
