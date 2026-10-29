from fractions import Fraction

import cardinals_schroeder_bernstein as sb


def test_chain_types_in_the_interval_example():
    F = Fraction
    assert sb.chain_type(F(1), sb.f1_inv, sb.g1_inv) == "A"
    assert sb.chain_type(F(1, 4), sb.f1_inv, sb.g1_inv) == "A"
    assert sb.chain_type(F(3, 4), sb.f1_inv, sb.g1_inv) == "B"
    assert sb.chain_type(F(1, 3), sb.f1_inv, sb.g1_inv) == "B"
    assert sb.chain_type(F(0), sb.f1_inv, sb.g1_inv) == "endless"


def test_interval_bijection_halves_powers_of_two_only():
    pts = sb.rational_points(30)
    for x in pts:
        y = sb.sb_map(x, sb.f1, sb.f1_inv, sb.g1_inv)
        q = x.denominator
        is_power = x.numerator == 1 and q & (q - 1) == 0  # x = 1/2^k
        assert y == (x / 2 if is_power else x)
        assert 0 <= y < 1
    images = [sb.sb_map(x, sb.f1, sb.f1_inv, sb.g1_inv) for x in pts]
    assert len(set(images)) == len(images)


def test_rational_points_are_distinct_and_in_range():
    pts = sb.rational_points(6)
    assert pts[0] == 0 and pts[-1] == 1
    assert len(pts) == len(set(pts)) == 13  # 1 + sum of Euler phi(q), q <= 6


def test_naturals_to_integers_bijection_window():
    h = [sb.sb_map(n, sb.f2, sb.f2_inv, sb.g2_inv) for n in range(3000)]
    assert len(set(h)) == len(h)
    assert set(range(-200, 201)) <= set(h)
    assert h[:6] == [0, 1, -1, 3, 4, -2]


def test_g2_is_an_injection_with_the_stated_inverse():
    values = {}
    for z in range(-500, 501):
        n = 3 * z if z >= 0 else -3 * z - 1
        assert n >= 0 and n not in values
        values[n] = z
        assert sb.g2_inv(n) == z
    assert sb.g2_inv(1) is None and sb.g2_inv(4) is None
