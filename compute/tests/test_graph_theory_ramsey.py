import math

import graph_theory_ramsey as gr


def test_masks_have_three_edges_and_right_count():
    for n in (3, 4, 5, 6):
        masks = gr.triangle_masks(n)
        assert len(masks) == math.comb(n, 3)
        assert all(bin(m).count("1") == 3 for m in masks)


def test_every_colouring_of_k6_has_two_mono_triangles():
    counts = gr.census(6)
    assert len(counts) == 2 ** 15
    assert min(counts) == 2
    # all red or all blue: every one of the 20 triangles is monochromatic
    assert counts[0] == counts[-1] == 20


def test_k5_good_colourings_are_pentagons():
    good = [c for c, t in enumerate(gr.census(5)) if t == 0]
    assert len(good) == 12
    assert all(gr.red_graph_is_five_cycle(c) for c in good)
    # complements of good colourings are good
    full = (1 << 10) - 1
    assert sorted(full ^ c for c in good) == sorted(good)


def test_erdos_bound_values():
    assert gr.erdos_bound(4) == 6
    assert gr.erdos_bound(10) == 100
    for k in range(4, 12):
        n = gr.erdos_bound(k)
        assert 2 * math.comb(n, k) < 2 ** math.comb(k, 2)
        assert 2 * math.comb(n + 1, k) >= 2 ** math.comb(k, 2)
        assert n >= 2 ** (k / 2)  # Erdos: R(k, k) > 2^(k/2) for k >= 3


def test_mono_triangles_small_cases():
    masks = gr.triangle_masks(3)
    assert gr.mono_triangles(0b000, masks) == 1
    assert gr.mono_triangles(0b011, masks) == 0
