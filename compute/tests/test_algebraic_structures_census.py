import algebraic_structures_census as ac


def test_number_of_tables_and_known_counts():
    counts, max_ids, max_invs = ac.census()
    assert counts["tables"] == 3 ** 9
    # OEIS A023814: associative operations on a 3-element set.
    assert counts["associative"] == 113
    # An identity e fixes 5 of the 9 entries; the other 4 are free.
    assert counts["with identity"] == 3 * 3 ** 4
    assert counts["groups"] == 3
    assert counts["groups"] <= counts["commutative monoids"] <= counts["monoids"]
    assert max_ids == 1 and max_invs == 1


def test_two_element_census():
    counts, max_ids, max_invs = ac.census(2)
    assert counts["tables"] == 16
    assert counts["associative"] == 8
    # Z/2 under + (identity 0) and under the relabelling with identity 1.
    assert counts["groups"] == 2
    assert max_ids <= 1 and max_invs <= 1


def test_helpers_on_addition_mod_3():
    op = {(a, b): (a + b) % 3 for a in ac.S for b in ac.S}
    assert ac.is_associative(op) and ac.is_commutative(op)
    assert ac.identities(op) == [0]
    assert [ac.inverses(op, a, 0) for a in ac.S] == [[0], [2], [1]]


def test_subtraction_is_not_associative_and_has_no_identity():
    op = {(a, b): (a - b) % 3 for a in ac.S for b in ac.S}
    assert not ac.is_associative(op)
    assert ac.identities(op) == []  # 0 is only a right identity


def test_units_and_fields():
    assert ac.units_mod(12) == [1, 5, 7, 11]
    assert ac.units_mod(1) == [0]  # in Z/1Z, 0 = 1
    assert not ac.is_field_mod(1)
    fields = [n for n in range(2, 30) if ac.is_field_mod(n)]
    assert fields == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert all(ac.is_field_mod(n) == ac.is_prime(n) for n in range(1, 60))
