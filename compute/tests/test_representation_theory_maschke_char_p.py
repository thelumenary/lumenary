import representation_theory_maschke_char_p as mc


def test_lines_count():
    for p in (2, 3, 5, 7, 11):
        assert len(mc.lines(p)) == p + 1


def test_shear_has_order_p_and_one_invariant_line():
    for p in (2, 3, 5, 7, 11):
        assert mc.order(mc.SHEAR, p) == p
        assert mc.invariant_lines(mc.SHEAR, p) == [(1, 0)]


def test_swap_invariant_lines():
    assert mc.invariant_lines(mc.SWAP, 2) == [(1, 1)]
    for p in (3, 5, 7):
        assert mc.invariant_lines(mc.SWAP, p) == [(1, 1), (1, p - 1)]


def test_averaging():
    for p in (3, 5, 7):
        e = mc.averaged(p)
        assert mc.matmul(e, e, p) == e
        assert mc.matmul(e, mc.SWAP, p) == mc.matmul(mc.SWAP, e, p)
    e2 = mc.averaged(2)
    assert mc.matmul(e2, e2, 2) != e2


def test_projection_is_a_projection():
    assert mc.matmul(mc.PI, mc.PI, 7) == mc.PI
    assert mc.on_line((2, 4), (1, 2), 7)
    assert not mc.on_line((1, 0), (0, 1), 5)
