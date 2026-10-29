import categories_monos_epis as cm


def test_functions_counts():
    assert cm.functions(0, 3) == [()]
    assert cm.functions(2, 0) == []
    assert len(cm.functions(3, 2)) == 8
    assert len(cm.functions(2, 3)) == 9


def test_compose_is_first_f_then_g():
    f = (1, 0, 1)        # 3 -> 2
    g = (2, 0)           # 2 -> 3
    assert cm.compose(g, f) == (0, 2, 0)


def test_mono_and_epi_match_injective_and_surjective():
    for m in range(4):
        for n in range(4):
            for f in cm.functions(m, n):
                assert cm.is_mono(f, n, (0, 1, 2)) == cm.is_injective(f)
                assert cm.is_epi(f, n, (0, 1, 2)) == cm.is_surjective(f, n)


def test_one_element_test_set_is_not_enough_for_epis():
    # Every map passes the epi test against T with one element.
    assert all(cm.is_epi(f, 3, (1,)) for f in cm.functions(2, 3))
    # With a two-element T only surjections pass.
    assert not any(cm.is_epi(f, 3, (2,)) for f in cm.functions(2, 3))


def test_tally_known_values():
    # 3 -> 3: 27 maps, 6 bijections, which are both mono and epi.
    assert cm.tally(3, 3) == (27, 6, 6, 6, 6)
    # 3 -> 2: 8 maps, no injections, 6 surjections.
    assert cm.tally(3, 2) == (8, 0, 0, 6, 6)
    # The empty map 0 -> n is always injective, surjective only for n = 0.
    assert cm.tally(0, 2) == (1, 1, 1, 0, 0)
    assert cm.tally(0, 0) == (1, 1, 1, 1, 1)
