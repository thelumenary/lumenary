import random
from fractions import Fraction

import pytest

import measure_theoretic_probability_polya_urn as pu


def test_red_distribution_is_uniform():
    for n in range(0, 25):
        dist = pu.red_distribution(n)
        assert sorted(dist) == list(range(1, n + 2))
        assert all(p == Fraction(1, n + 1) for p in dist.values())
    with pytest.raises(ValueError):
        pu.red_distribution(-1)


def test_martingale_identity_exact():
    for n in range(40):
        for r in range(1, n + 2):
            assert pu.martingale_defect(n, r) == 0


def test_expected_fraction_is_constant():
    for n in range(15):
        dist = pu.red_distribution(n)
        mean = sum(p * Fraction(r, n + 2) for r, p in dist.items())
        assert mean == Fraction(1, 2)


def test_run_urn_bounds_and_determinism():
    path = pu.run_urn(500, random.Random(7))
    assert len(path) == 500
    assert all(0 < x < 1 for x in path)
    assert path == pu.run_urn(500, random.Random(7))
    # increments shrink: |M_(n+1) - M_n| <= 1/(n+3)
    full = [0.5] + path
    assert all(abs(b - a) <= 1 / (k + 3) + 1e-12
               for k, (a, b) in enumerate(zip(full, full[1:])))
