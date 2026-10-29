import math

import order_theory_counting_posets as cp


def test_known_counts():
    expected = {1: (1, 1, 1), 2: (4, 3, 2), 3: (29, 19, 6), 4: (355, 219, 24)}
    for n, (pre, part, total) in expected.items():
        c = cp.census(n)
        assert (c["preorders"], c["partial orders"], c["total orders"]) == (pre, part, total)
        assert c["total orders"] == math.factorial(n)
        assert c["max ok"]


def test_lattice_and_greatest_counts():
    # n = 4: 24 chains plus 12 labellings of the diamond (Boolean lattice 2 x 2).
    assert cp.census(4)["lattices"] == 36
    # A poset with a greatest element: choose the top, then any poset on the rest.
    assert cp.census(3)["with greatest"] == 3 * 3
    assert cp.census(4)["with greatest"] == 4 * 19


def test_properties_on_examples():
    chain = {(a, b) for a in range(3) for b in range(3) if a <= b}
    assert cp.is_transitive(chain, 3) and cp.is_antisymmetric(chain) and cp.is_total(chain, 3)
    assert cp.maximal_elements(chain, 3) == [2] and cp.greatest_element(chain, 3) == 2
    assert cp.is_lattice(chain, 3)
    vee = {(0, 0), (1, 1), (2, 2), (0, 1), (0, 2)}
    assert cp.maximal_elements(vee, 3) == [1, 2]
    assert cp.greatest_element(vee, 3) is None
    assert cp.join(vee, 3, 1, 2) is None and cp.meet(vee, 3, 1, 2) == 0
    assert not cp.is_lattice(vee, 3)


def test_non_examples():
    cycle = {(0, 0), (1, 1), (0, 1), (1, 0)}
    assert cp.is_transitive(cycle, 2) and not cp.is_antisymmetric(cycle)  # a preorder only
    broken = {(0, 0), (1, 1), (2, 2), (0, 1), (1, 2)}
    assert not cp.is_transitive(broken, 3)
    assert sum(1 for _ in cp.reflexive_relations(3)) == 2 ** 6
