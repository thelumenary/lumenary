import math
import random

import probabilistic_method_chernoff as pc


def test_exact_tail_small_cases():
    assert pc.exact_tail(2, 2) == 0.25           # both signs +1
    assert pc.exact_tail(2, 0) == 0.75
    assert pc.exact_tail(10, -10) == 1.0
    assert pc.exact_tail(4, 5) == 0.0


def test_bounds_dominate_exact_tail():
    for n in (10, 50, 100, 400):
        for a in range(1, n + 1, max(1, n // 20)):
            exact = pc.exact_tail(n, a)
            assert exact <= pc.chernoff_bound(n, a) + 1e-15
            assert exact <= pc.chebyshev_bound(n, a) + 1e-15


def test_chernoff_beats_chebyshev_far_out():
    n = 100
    assert pc.chernoff_bound(n, 40) < pc.chebyshev_bound(n, 40) / 100


def test_simulation_close_to_exact():
    rng = random.Random(11)
    sim = pc.simulate_tail(100, 20, 20000, rng)
    assert abs(sim - pc.exact_tail(100, 20)) < 0.006


def test_imbalance_and_sets():
    sets = [[0, 1, 2], [1, 3]]
    assert pc.max_imbalance([1, 1, 1, -1], sets) == 3
    assert pc.max_imbalance([1, -1, 1, 1], sets) == 1
    rng = random.Random(3)
    s = pc.random_sets(64, 10, rng)
    assert len(s) == 10 and all(0 <= i < 64 for a in s for i in a)


def test_random_colourings_usually_balance_sets():
    rng = random.Random(8)
    n = 64
    sets = pc.random_sets(n, n, rng)
    bound = math.sqrt(2 * n * math.log(2 * n))
    good = sum(pc.max_imbalance([rng.choice((-1, 1)) for _ in range(n)],
                                sets) <= bound for _ in range(100))
    assert good >= 90
