from decimal import Decimal

import numerical_methods_root_finding as rf

ROOT2 = Decimal(2).sqrt()


def f(x):
    return x * x - 2


def test_bisection_error_bound():
    mids = rf.bisection(f, Decimal(1), Decimal(2), 30)
    for n, m in enumerate(mids):
        assert abs(m - ROOT2) <= Decimal(1) / Decimal(2) ** (n + 1)


def test_newton_quadratic():
    xs = rf.newton(f, lambda x: 2 * x, Decimal(2), 6)
    errs = [float(abs(x - ROOT2)) for x in xs]
    assert errs[-1] < 1e-45
    assert all(1.9 < p < 2.1 for p in rf.orders(errs[1:5]))


def test_secant_golden_order():
    xs = rf.secant(f, Decimal(2), Decimal(1), 7)
    errs = [float(abs(x - ROOT2)) for x in xs[2:]]
    assert abs(rf.orders(errs)[-1] - 1.618) < 0.05


def test_secant_stops_on_equal_values():
    xs = rf.secant(lambda x: x * 0 + 1, Decimal(0), Decimal(1), 5)
    assert xs == [Decimal(0), Decimal(1)]


def test_double_root_linear_and_cycle():
    xs = rf.newton(lambda x: (x - 1) ** 2, lambda x: 2 * (x - 1), Decimal(2), 5)
    assert [x - 1 for x in xs] == [Decimal(1) / 2 ** k for k in range(6)]
    cyc = rf.newton(lambda x: x ** 3 - 2 * x + 2, lambda x: 3 * x * x - 2, Decimal(0), 4)
    assert cyc == [0, 1, 0, 1, 0]


def test_orders_on_exact_sequences():
    assert all(abs(p - 2) < 1e-12 for p in rf.orders([1e-1, 1e-2, 1e-4, 1e-8]))
    assert all(abs(p - 1) < 1e-12 for p in rf.orders([0.5, 0.25, 0.125, 0.0625]))
