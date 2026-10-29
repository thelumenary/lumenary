import math
import random

import pytest

import gauge_theory_chern_number as gc


def test_reduce_angle_range():
    for t in [0.0, math.pi, -math.pi, 3 * math.pi, 7.5, -12.0, 1e-9]:
        r = gc.reduce_angle(t)
        assert -math.pi < r <= math.pi
        k = (t - r) / (2 * math.pi)
        assert k == pytest.approx(round(k), abs=1e-12)
    assert gc.reduce_angle(math.pi) == pytest.approx(math.pi)
    assert gc.reduce_angle(-math.pi) == pytest.approx(math.pi)


@pytest.mark.parametrize("n,k", [(6, 1), (8, -2), (10, 5), (12, 0)])
def test_charge_k_field_has_uniform_flux_and_charge_k(n, k):
    ax, ay = gc.charge_k_field(n, k)
    b = 2 * math.pi * k / n ** 2
    for row in gc.plaquettes(ax, ay):
        for t in row:
            assert t == pytest.approx(b, abs=1e-12)
    assert gc.charge(ax, ay) == pytest.approx(k, abs=1e-12)


def test_gauge_invariance():
    rng = random.Random(5)
    n = 8
    field = gc.charge_k_field(n, 3)
    lam = [[rng.uniform(-10, 10) for _ in range(n)] for _ in range(n)]
    moved = gc.gauge_transform(*field, lam)
    assert gc.max_plaquette_change(field, moved) < 1e-12
    assert gc.charge(*moved) == pytest.approx(3, abs=1e-12)


def test_charge_is_always_an_integer_even_for_random_fields():
    rng = random.Random(9)
    n = 6
    for _ in range(20):
        ax = [[rng.uniform(-5, 5) for _ in range(n)] for _ in range(n)]
        ay = [[rng.uniform(-5, 5) for _ in range(n)] for _ in range(n)]
        q = gc.charge(ax, ay)
        assert q == pytest.approx(round(q), abs=1e-9)


def test_small_noise_keeps_charge_and_naive_charge_is_not_integer():
    rng = random.Random(1)
    base = gc.charge_k_field(10, 2)
    for _ in range(10):
        assert round(gc.charge(*gc.add_noise(*base, 0.05, rng))) == 2
    naive = gc.naive_charge(*base)
    assert abs(naive - 2) > 1e-3
    assert naive < 2
