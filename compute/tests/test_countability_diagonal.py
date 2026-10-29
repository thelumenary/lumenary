from decimal import Decimal
from fractions import Fraction

import countability_diagonal as cd


def test_subsets_count_and_content():
    assert cd.subsets([]) == [frozenset()]
    ps = cd.subsets([0, 1, 2])
    assert len(ps) == 8 and len(set(ps)) == 8
    assert frozenset({0, 2}) in ps


def test_diagonal_set():
    f = {0: frozenset({0, 1}), 1: frozenset(), 2: frozenset({2})}
    assert cd.diagonal_set(f, [0, 1, 2]) == frozenset({1})


def test_cantor_finite_cases():
    for n in range(4):
        total, missed, onto = cd.check_cantor(n)
        assert total == (2 ** n) ** n
        assert missed == total      # the diagonal set is always missed
        assert onto == 0            # so nothing is onto P(A)


def test_digits_canonical_expansion():
    assert cd.digits(Fraction(1, 2), 4) == [5, 0, 0, 0]       # not 4999
    assert cd.digits(Fraction(1, 7), 6) == [1, 4, 2, 8, 5, 7]
    assert cd.digits(Fraction(0), 3) == [0, 0, 0]
    assert cd.digits(Decimal(2).sqrt() - 1, 5) == [4, 1, 4, 2, 1]


def test_diagonal_digits_rule():
    rows = [[5, 1, 2], [0, 5, 3], [9, 9, 4]]
    assert cd.diagonal_digits(rows) == [4, 4, 5]
    named = cd.numbers()
    rows = [cd.digits(x, 10) for _, x in named]
    diag = cd.diagonal_digits(rows)
    assert all(d in (4, 5) for d in diag)
    assert all(diag[n] != rows[n][n] for n in range(10))
