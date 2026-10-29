import pytest

import fields_galois_irreducible_counts as fc


def test_mobius():
    assert [fc.mobius(n) for n in range(1, 13)] == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]


@pytest.mark.parametrize("p, n, expected", [(2, 1, 2), (2, 2, 1), (2, 3, 2), (2, 4, 3), (2, 8, 30), (3, 2, 3), (5, 2, 10)])
def test_gauss_formula_values(p, n, expected):
    assert fc.gauss_count(p, n) == expected


def test_sieve_matches_formula():
    for p, top in ((2, 7), (3, 4), (5, 2), (7, 2)):
        for n in range(1, top + 1):
            assert len(fc.irreducibles(p, n)) == fc.gauss_count(p, n)


def test_specific_irreducibles():
    assert sorted(fc.irreducibles(2, 2)) == [(1, 1, 1)]          # x^2 + x + 1
    assert (1, 0, 1) in fc.irreducibles(3, 2)                     # x^2 + 1 over F_3
    assert (1, 0, 1) not in fc.irreducibles(2, 2)                 # (x + 1)^2 over F_2
    assert (1, 0, 1, 0, 1) not in fc.irreducibles(2, 4)           # (x^2 + x + 1)^2


def test_degree_identity():
    for p, n in ((2, 6), (3, 4)):
        assert sum(d * fc.gauss_count(p, d) for d in range(1, n + 1) if n % d == 0) == p ** n


def test_poly_mul_and_show():
    assert fc.poly_mul((1, 1), (1, 1), 2) == (1, 0, 1)
    assert fc.show((1, 1, 0, 1)) == "x^3+x+1"
