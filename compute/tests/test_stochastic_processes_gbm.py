import math
import random

import pytest

import stochastic_processes_gbm as gbm


def test_exact_solution_values():
    assert gbm.exact_solution(1.0, 0.1, 0.0, 2.0, 5.0) == pytest.approx(math.exp(0.2))
    assert gbm.exact_solution(2.0, 0.3, 0.5, 0.0, 0.0) == 2.0


def test_euler_without_noise_is_compound_interest():
    n = 1000
    s = gbm.euler_maruyama(1.0, 0.05, 0.4, [0.0] * n, 1 / n)
    assert s == pytest.approx((1 + 0.05 / n) ** n)
    assert s == pytest.approx(math.exp(0.05), rel=1e-4)


def test_coarsen_preserves_total_increment():
    rng = random.Random(5)
    inc = [rng.gauss(0, 1) for _ in range(64)]
    for f in [1, 2, 8, 64]:
        c = gbm.coarsen(inc, f)
        assert len(c) == 64 // f
        assert math.fsum(c) == pytest.approx(math.fsum(inc))


def test_strong_error_decreases_with_step():
    rng = random.Random(6)
    fine = 256
    incs = [[rng.gauss(0, math.sqrt(1 / fine)) for _ in range(fine)] for _ in range(200)]
    def err(n):
        return sum(abs(gbm.euler_maruyama(1.0, 0.1, 0.4, gbm.coarsen(inc, fine // n), 1 / n)
                       - gbm.exact_solution(1.0, 0.1, 0.4, 1.0, math.fsum(inc)))
                   for inc in incs) / len(incs)
    assert err(256) < err(16) < err(2)
