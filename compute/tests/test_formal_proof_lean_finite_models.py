import formal_proof_lean_finite_models as fm


def test_counts():
    assert len(fm.functions(2, 3)) == 9
    assert len(fm.functions(0, 2)) == 1  # the empty function
    assert len(fm.subsets(3)) == 8
    assert len(fm.relations(2, 2)) == 16


def test_image_and_injective():
    f = (1, 0, 1)
    assert fm.image(f, frozenset({0, 2})) == frozenset({1})
    assert not fm.is_injective(f)
    assert fm.is_injective((2, 0, 1))


def test_intersections_iff_injective():
    for a in range(4):
        for b in range(1, 4):
            for f in fm.functions(a, b):
                assert fm.preserves_intersections(f) == fm.is_injective(f)


def test_composition_facts():
    f, g = (0,), (0, 0)
    assert fm.is_injective(fm.compose(g, f)) and not fm.is_injective(g)
    for f in fm.functions(2, 3):
        for g in fm.functions(3, 3):
            if fm.is_injective(fm.compose(g, f)):
                assert fm.is_injective(f)


def test_quantifier_order():
    eq = frozenset({(0, 0), (1, 1)})
    assert fm.forall_exists(eq, 2, 2) and not fm.exists_forall(eq, 2, 2)
    for rel in fm.relations(2, 3):
        if fm.exists_forall(rel, 2, 3):
            assert fm.forall_exists(rel, 2, 3)
