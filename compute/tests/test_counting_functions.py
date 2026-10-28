from math import factorial

import pytest

import counting_functions as cf


def test_all_functions_lists_each_function_once():
    fs = cf.all_functions("ab", "xyz")
    assert len(fs) == 9
    assert len({tuple(sorted(f.items())) for f in fs}) == 9
    assert all(set(f) == {"a", "b"} and set(f.values()) <= set("xyz") for f in fs)


def test_empty_domain_has_exactly_the_empty_function():
    assert cf.all_functions([], [1, 2]) == [{}]
    assert cf.all_functions([], []) == [{}]


def test_nonempty_domain_to_empty_codomain_has_no_functions():
    assert cf.all_functions([1], []) == []


def test_injective_surjective_bijective_predicates():
    assert cf.is_injective({1: "a", 2: "b"})
    assert not cf.is_injective({1: "a", 2: "a"})
    assert cf.is_injective({})
    assert cf.is_surjective({1: "a", 2: "b"}, "ab")
    assert not cf.is_surjective({1: "a", 2: "a"}, "ab")
    assert cf.is_surjective({}, [])
    assert not cf.is_surjective({}, [1])
    assert cf.is_bijective({1: "b", 2: "a"}, "ab")
    assert not cf.is_bijective({1: "a"}, "ab")


@pytest.mark.parametrize("n,k,expected", [(5, 0, 1), (5, 1, 5), (5, 2, 20), (5, 5, 120), (3, 4, 0), (0, 0, 1), (0, 1, 0)])
def test_falling_factorial(n, k, expected):
    assert cf.falling_factorial(n, k) == expected


def test_falling_factorial_rejects_negative():
    with pytest.raises(ValueError):
        cf.falling_factorial(-1, 2)


@pytest.mark.parametrize("m,n,expected", [(0, 0, 1), (0, 1, 0), (1, 0, 0), (3, 2, 6), (4, 2, 14), (4, 3, 36), (5, 3, 150), (2, 3, 0)])
def test_surjection_formula_known_values(m, n, expected):
    assert cf.surjection_formula(m, n) == expected


def test_surjection_formula_rejects_negative():
    with pytest.raises(ValueError):
        cf.surjection_formula(2, -1)


@pytest.mark.parametrize("m", range(0, 5))
@pytest.mark.parametrize("n", range(0, 5))
def test_enumeration_matches_formulas(m, n):
    assert cf.count_by_enumeration(m, n) == cf.formula_counts(m, n)


@pytest.mark.parametrize("n", range(0, 6))
def test_bijections_of_an_n_set(n):
    assert cf.count_by_enumeration(n, n)["bijective"] == factorial(n)


def test_specific_counts():
    assert cf.count_by_enumeration(3, 2) == {"all": 8, "injective": 0, "surjective": 6, "bijective": 0}
    assert cf.count_by_enumeration(2, 3) == {"all": 9, "injective": 6, "surjective": 0, "bijective": 0}
