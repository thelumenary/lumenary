import math

import systematic_listing_trees as st


def test_tree_list_outfits():
    outfits = st.tree_list(st.SHIRTS, st.TROUSERS)
    assert len(outfits) == 6
    assert outfits[0] == ("red", "black") and outfits[-1] == ("yellow", "brown")
    assert len(set(outfits)) == 6
    for s in st.SHIRTS:
        for t in st.TROUSERS:
            assert (s, t) in outfits


def test_product_rule():
    assert st.product_rule_holds(6)
    assert st.tree_list([], ["x"]) == []
    assert len(st.tree_list(range(4), range(7))) == 28


def test_rows_are_factorials():
    assert st.rows("ABC") == ["ABC", "ACB", "BAC", "BCA", "CAB", "CBA"]
    for n in range(1, 7):
        letters = "ABCDEF"[:n]
        assert len(st.rows(letters)) == math.factorial(n)
        assert len(set(st.rows(letters))) == math.factorial(n)


def test_handshakes_formula():
    for n in range(0, 12):
        assert len(st.handshakes(n)) == n * (n - 1) // 2
    assert st.handshakes(3) == [(1, 2), (1, 3), (2, 3)]


def test_ordered_pairs_double_count():
    for n in range(1, 10):
        assert len(st.ordered_pairs(n)) == 2 * len(st.handshakes(n))
    assert (2, 1) in st.ordered_pairs(2) and (1, 2) in st.ordered_pairs(2)
    assert all(i != j for i, j in st.ordered_pairs(5))
