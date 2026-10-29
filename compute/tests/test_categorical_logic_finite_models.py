import math

import categorical_logic_finite_models as fm


def test_all_maps_and_powers():
    assert len(fm.all_maps(3)) == 27
    f = (1, 2, 0)  # a 3-cycle
    assert fm.compose_power(f, 0) == (0, 1, 2)
    assert fm.compose_power(f, 1) == f
    assert fm.compose_power(f, 3) == (0, 1, 2)
    g = (1, 2, 2)  # 0 -> 1 -> 2 -> 2
    assert fm.compose_power(g, 2) == (2, 2, 2)


def test_numeral_meanings_distinguish_small_numerals():
    # Over 3 points, numerals 0..7 all have different meanings.
    meanings = [fm.numeral_meaning(n, 3) for n in range(8)]
    assert len(set(meanings)) == 8
    assert fm.numeral_meaning(2, 3) == fm.numeral_meaning(8, 3)


def test_first_coincidence_matches_index_and_period():
    # The full transformation monoid on m points satisfies x^(m-1) = x^(m-1+L)
    # with L = lcm(1..m), and no earlier identity of this form.
    for m in range(1, 5):
        a, b = fm.first_coincidence(m)
        assert a == m - 1
        assert b - a == math.lcm(*range(1, m + 1))


def test_exactly_four_natural_pair_maps():
    natural = fm.natural_pair_maps(2)
    assert len(natural) == 4
    pts = [(a, b) for a in range(2) for b in range(2)]
    tables = {tuple(g[p] for p in pts) for g in natural}
    definable = {tuple(t(*p) for p in pts)
                 for t in fm.definable_pair_maps().values()}
    assert tables == definable


def test_a_non_natural_map_is_rejected():
    # The constant map to (0, 0) is not natural: renaming 0 <-> 1 breaks it.
    pts = [(a, b) for a in range(2) for b in range(2)]
    constant = {p: (0, 0) for p in pts}
    swap = (1, 0)
    a, b = 0, 1
    lhs = constant[(swap[a], swap[b])]
    rhs = (swap[constant[(a, b)][0]], swap[constant[(a, b)][1]])
    assert lhs != rhs
    assert constant not in fm.natural_pair_maps(2)
