import itertools
import random

import complexity_theory_sat_threshold as st


def brute_force_sat(formula, n):
    for bits in itertools.product((False, True), repeat=n):
        lits = {v if bits[v - 1] else -v for v in range(1, n + 1)}
        if st.verify(formula, lits):
            return True
    return False


def test_dpll_agrees_with_brute_force():
    rng = random.Random(11)
    for _ in range(150):
        n = rng.randint(3, 8)
        m = rng.randint(1, 6 * n)
        formula = st.random_3cnf(n, m, rng)
        result = st.dpll(formula, {"nodes": 0})
        assert (result is not None) == brute_force_sat(formula, n)
        if result is not None:
            assert st.verify(formula, st.complete(result, n))


def test_verify_rejects_and_accepts():
    formula = [(1, 2, 3), (-1, -2, 3)]
    assert st.verify(formula, {1, -2, 3})
    assert not st.verify(formula, {-1, -2, -3})


def test_unsatisfiable_core_is_refuted():
    core = [(a * 1, b * 2, c * 3) for a in (1, -1) for b in (1, -1) for c in (1, -1)]
    stats = {"nodes": 0}
    assert st.dpll(core, stats) is None
    assert stats["nodes"] >= 3


def test_sweep_shape_and_monotone_trend():
    rows = st.sweep(n=12, ratios=(2, 8), trials=20, seed=3)
    (r1, m1, f1, _, bad1), (r2, m2, f2, _, bad2) = rows
    assert (m1, m2) == (24, 96)
    assert f1 > 0.9 and f2 < 0.1
    assert bad1 == bad2 == 0


def test_complete_fills_every_variable():
    full = st.complete({1, -3}, 4)
    assert full == {1, -2, -3, -4}
