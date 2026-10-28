from math import gcd

import pytest

import clock_arithmetic as ca


def test_tables_mod_1_and_mod_2():
    assert ca.add_table(1) == [[0]]
    assert ca.mul_table(1) == [[0]]
    assert ca.add_table(2) == [[0, 1], [1, 0]]
    assert ca.mul_table(2) == [[0, 0], [0, 1]]


@pytest.mark.parametrize("k", [0, -3])
def test_tables_reject_bad_modulus(k):
    with pytest.raises(ValueError):
        ca.add_table(k)
    with pytest.raises(ValueError):
        ca.mul_table(k)
    with pytest.raises(ValueError):
        ca.inverse_by_search(1, k)


@pytest.mark.parametrize("k", range(1, 13))
def test_tables_are_latin_and_symmetric(k):
    add, mul = ca.add_table(k), ca.mul_table(k)
    assert all(sorted(row) == list(range(k)) for row in add), "each row of + is a permutation"
    assert all(add[a][b] == add[b][a] and mul[a][b] == mul[b][a] for a in range(k) for b in range(k))


def test_inverse_by_search_examples():
    assert ca.inverse_by_search(5, 6) == 5
    assert ca.inverse_by_search(2, 6) is None
    assert ca.inverse_by_search(3, 7) == 5
    assert ca.inverse_by_search(0, 7) is None


def test_mod_one_edge_case():
    # Mod 1 everything equals 0, and 0 * 0 = 0 = 1 (mod 1): the single residue is invertible.
    assert ca.inverse_by_search(0, 1) == 0
    assert ca.invertible_residues(1) == ca.coprime_residues(1) == [0]


def test_invertible_residues_examples():
    assert ca.invertible_residues(6) == [1, 5]
    assert ca.invertible_residues(7) == [1, 2, 3, 4, 5, 6]
    assert ca.invertible_residues(12) == [1, 5, 7, 11]


@pytest.mark.parametrize("k", range(2, 31))
def test_inverses_exist_exactly_when_coprime(k):
    assert ca.invertible_residues(k) == [a for a in range(k) if gcd(a, k) == 1]
    for a in ca.invertible_residues(k):
        assert a * ca.inverse_by_search(a, k) % k == 1


def test_inverse_by_pow():
    assert ca.inverse_by_pow(3, 7) == 5
    assert ca.inverse_by_pow(2, 6) is None
    assert ca.inverse_by_pow(0, 1) == 0


def test_compare_up_to_finds_no_disagreement():
    assert ca.compare_up_to(30) == []
    assert ca.compare_up_to(5, k_min=1) == []


def test_euler_phi_values():
    assert [len(ca.coprime_residues(k)) for k in range(2, 17)] == [1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8]


def test_format_side_by_side_shape():
    lines = ca.format_side_by_side(6)
    assert len(lines) == 2 + 6
    # Row 0: "+" row is 0..5, then the "x" row label 0, then the "x" row of zeros.
    cells = lines[2].split("|")
    assert cells[0].strip() == "0"
    assert cells[1].split() == ["0", "1", "2", "3", "4", "5", "0"]
    assert cells[2].split() == ["0"] * 6
    assert lines[7].split("|")[2].split() == ["0", "5", "4", "3", "2", "1"]
