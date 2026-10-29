import pytest

import elementary_number_theory_pell as pell


def test_continued_fractions():
    assert pell.sqrt_continued_fraction(2) == (1, [2])
    assert pell.sqrt_continued_fraction(7) == (2, [1, 1, 1, 4])
    assert pell.sqrt_continued_fraction(13) == (3, [1, 1, 1, 1, 6])
    with pytest.raises(ValueError):
        pell.sqrt_continued_fraction(16)


@pytest.mark.parametrize("d, sol", [(2, (3, 2)), (3, (2, 1)), (13, (649, 180)), (61, (1766319049, 226153980))])
def test_fundamental_solutions(d, sol):
    assert pell.fundamental_solution(d) == sol


def test_solutions_satisfy_equation():
    for d in range(2, 200):
        if pell.isqrt(d) ** 2 != d:
            x, y = pell.fundamental_solution(d)
            assert x * x - d * y * y == 1 and y > 0


def test_brute_force_agrees():
    for d in range(2, 31):
        if pell.isqrt(d) ** 2 != d:
            assert pell.brute_force(d, 2000) == pell.fundamental_solution(d)


def test_composition():
    s = (3, 2)
    assert pell.compose(s, s, 2) == (17, 12)
    x, y = pell.compose((649, 180), (649, 180), 13)
    assert x * x - 13 * y * y == 1
