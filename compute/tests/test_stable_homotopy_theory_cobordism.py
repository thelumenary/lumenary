import stable_homotopy_theory_cobordism as c


def test_partitions_and_thom_ranks():
    assert len(c.partitions(5)) == 7
    assert c.partitions(0) == [()]
    assert [c.thom_rank(n) for n in range(11)] == [1, 0, 1, 0, 2, 1, 3, 1, 5, 3, 8]


def test_mersenne_detection():
    assert [i for i in range(1, 40) if c.is_mersenne(i)] == [1, 3, 7, 15, 31]


def test_projective_space_sw_numbers():
    # w(RP^n) = (1 + u)^(n + 1): RP^2 and RP^4 do not bound, odd RP^n do.
    assert c.sw_number((2,), (2,)) == 1
    assert c.sw_number((2,), (1, 1)) == 1
    assert c.sw_number((4,), (4,)) == 1          # Euler characteristic mod 2
    for n in (1, 3, 5, 7):
        assert all(c.sw_number((n,), p) == 0 for p in c.partitions(n))


def test_product_formula_euler_characteristic():
    # w_top of a product is the product of the w_top's (Euler classes mod 2).
    assert c.sw_number((2, 2), (4,)) == 1
    assert c.sw_number((2, 1), (3,)) == 0


def test_rank_matches_thom_in_even_degrees():
    for n in (2, 4, 6):
        parts = c.partitions(n)
        vectors = [[c.sw_number(d, p) for p in parts] for d in c.rp_products(n)]
        assert c.rank_mod2(vectors) == c.thom_rank(n)


def test_rank_mod2():
    assert c.rank_mod2([[1, 0], [0, 1], [1, 1]]) == 2
    assert c.rank_mod2([[0, 0]]) == 0
