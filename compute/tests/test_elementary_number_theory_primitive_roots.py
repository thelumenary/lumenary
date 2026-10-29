import pytest

import elementary_number_theory_primitive_roots as pr


@pytest.mark.parametrize("n, phi", [(1, 1), (2, 1), (8, 4), (9, 6), (12, 4), (36, 12), (97, 96)])
def test_totient(n, phi):
    assert pr.totient(n) == phi


def test_multiplicative_order():
    assert pr.multiplicative_order(3, 7) == 6
    assert pr.multiplicative_order(2, 7) == 3
    assert [pr.multiplicative_order(a, 8) for a in (1, 3, 5, 7)] == [1, 2, 2, 2]
    assert pr.multiplicative_order(10, 7) == 6


def test_least_primitive_roots():
    assert [pr.primitive_root(p) for p in (3, 5, 7, 11, 13, 17, 23, 41)] == [2, 2, 3, 2, 2, 3, 5, 6]
    assert pr.primitive_root(8) is None
    assert pr.primitive_root(9) == 2
    assert pr.primitive_root(18) == 5


def test_classification_up_to_100():
    for n in range(1, 101):
        assert (pr.primitive_root(n) is not None) == pr.predicted(n), n


def test_predicted():
    assert [n for n in range(1, 20) if not pr.predicted(n)] == [8, 12, 15, 16]


def test_artin_share_is_plausible():
    hits, total = pr.two_is_primitive_share(10000)
    assert total == 1228
    assert abs(hits / total - pr.ARTIN_CONSTANT) < 0.02
