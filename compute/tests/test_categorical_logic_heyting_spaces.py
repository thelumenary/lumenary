import categorical_logic_heyting_spaces as hs


def test_topology_counts_match_known_values():
    # Numbers of labelled topologies on 0, 1, 2, 3, 4 points: 1, 1, 4, 29, 355.
    assert [len(hs.all_topologies(n)) for n in range(4)] == [1, 1, 4, 29]
    assert all(hs.is_topology(t, frozenset(range(3))) for t in hs.all_topologies(3))


def test_residuation_law_in_every_small_topology():
    for n in range(1, 4):
        assert all(hs.residuation_holds(t) for t in hs.all_topologies(n))


def test_boolean_topologies_are_partition_topologies():
    # Boolean open-set algebras on a finite set correspond to partitions:
    # Bell numbers 1, 2, 5.
    for n, bell in [(1, 1), (2, 2), (3, 5)]:
        space = frozenset(range(n))
        boolean = [t for t in hs.all_topologies(n) if hs.is_boolean(t, space)]
        assert len(boolean) == bell
        for t in boolean:
            # every open set is also closed
            assert all(space - u in t for u in t)


def test_sierpinski_negation():
    opens = frozenset([frozenset(), frozenset([1]), frozenset([0, 1])])
    u = frozenset([1])
    assert hs.neg(opens, u) == frozenset()
    assert hs.neg(opens, hs.neg(opens, u)) == frozenset([0, 1])
    assert hs.implies(opens, frozenset([0, 1]), u) == u
    # the discrete topology is Boolean
    discrete = frozenset(hs.subsets({0, 1}))
    assert hs.is_boolean(discrete, frozenset({0, 1}))


def test_intuitionistic_laws_have_no_small_countermodel():
    formulas = dict(hs.FORMULAS)
    assert hs.countermodel(formulas["not not (p or not p)"]) is None
    assert hs.countermodel(formulas["p -> not not p"]) is None


def test_classical_laws_have_countermodels():
    formulas = dict(hs.FORMULAS)
    for name in ["p or not p", "not not p -> p", "((p -> q) -> p) -> p"]:
        space, opens, val = hs.countermodel(formulas[name])
        assert len(space) == 2
        assert hs.evaluate(formulas[name], opens, val) != space
    # weak excluded middle and Dummett's law need three points
    for name in ["not p or not not p", "(p -> q) or (q -> p)"]:
        space, _, _ = hs.countermodel(formulas[name])
        assert len(space) == 3
        assert hs.countermodel(formulas[name], max_points=2) is None


def test_evaluate_and_atoms():
    opens = frozenset(hs.subsets({0, 1}))
    val = {"p": frozenset({0}), "q": frozenset({1})}
    assert hs.evaluate(("and", "p", "q"), opens, val) == frozenset()
    assert hs.evaluate(("or", "p", "q"), opens, val) == frozenset({0, 1})
    assert hs.atoms(("imp", ("not", "p"), ("or", "q", "p"))) == {"p", "q"}
