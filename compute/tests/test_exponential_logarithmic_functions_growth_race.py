import exponential_logarithmic_functions_growth_race as gr


def test_ratio_threshold():
    assert gr.ratio_below_two_from(1) == 2  # (1 + 1/n) < 2 needs n > 1
    assert gr.ratio_below_two_from(2) == 3
    assert gr.ratio_below_two_from(10) == 14
    # just below the threshold the ratio is still at least 2
    assert 15 ** 10 < 2 * 14 ** 10 and 14 ** 10 >= 2 * 13 ** 10


def test_crossovers():
    assert gr.crossover(2) == 5   # matches Lean's sq_lt_two_pow (n >= 5)
    assert gr.crossover(3) == 10
    assert gr.crossover(5) == 23
    assert gr.crossover(10) == 59


def test_crossover_is_sharp_and_holds_later():
    for k in (2, 3, 5, 10):
        n = gr.crossover(k)
        assert 2 ** (n - 1) <= (n - 1) ** k
        assert gr.holds_from(k, n, 600)


def test_small_n_exception_for_k_10():
    # 2^1 > 1^10, yet 2^n loses for 2 <= n <= 58: the crossover is not the first win.
    assert 2 ** 1 > 1 ** 10
    assert not gr.holds_from(10, 1, 58)


def test_folding():
    assert round(gr.folded_thickness_km(42)) == 439805
    assert abs(gr.folded_thickness_km(0) - 1e-7) < 1e-20
    assert gr.folded_thickness_km(10) == gr.folded_thickness_km(9) * 2
