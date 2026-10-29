import math

import arithmetic_geometry_point_counts as pc


def brute_force(coeffs, p):
    a1, a2, a3, a4, a6 = coeffs
    return 1 + sum(1 for x in range(p) for y in range(p)
                   if (y * y + a1 * x * y + a3 * y
                       - x ** 3 - a2 * x * x - a4 * x - a6) % p == 0)


def test_primes_below():
    assert pc.primes_below(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert len(pc.primes_below(1000)) == 168
    assert pc.primes_below(2) == []


def test_count_matches_brute_force():
    for name, (coeffs, _) in pc.CURVES.items():
        for p in pc.primes_below(60):
            assert pc.count_points(coeffs, p) == brute_force(coeffs, p), (name, p)


def test_known_traces_of_11a1():
    # a_p of 11a1 = coefficients of q * prod (1 - q^n)^2 (1 - q^(11n))^2
    coeffs = pc.CURVES["11a1"][0]
    known = {2: -2, 3: -1, 5: 1, 7: -2, 13: 4, 17: -2, 19: 0, 23: -1, 29: 0}
    for p, ap in known.items():
        assert pc.trace_of_frobenius(coeffs, p) == ap


def test_hasse_bound_all_curves():
    for coeffs, _ in pc.CURVES.values():
        for p in pc.primes_below(400):
            assert abs(pc.trace_of_frobenius(coeffs, p)) <= 2 * math.sqrt(p)


def test_sato_tate_density_is_a_probability():
    assert math.isclose(pc.sato_tate_mass(0, math.pi), 1.0)
    assert math.isclose(pc.sato_tate_mass(0, math.pi / 2), 0.5)
    assert pc.sato_tate_mass(0, 0.1) < pc.sato_tate_mass(1.5, 1.6)


def test_euler_products_checkpoints():
    coeffs = pc.CURVES["37a1"][0]
    primes = pc.primes_below(50)
    v = pc.euler_products(coeffs, [10, 49], primes)
    direct = 1.0
    for p in [2, 3, 5, 7]:
        direct *= pc.count_points(coeffs, p) / p
    assert math.isclose(v[0], direct)
    assert len(v) == 2
