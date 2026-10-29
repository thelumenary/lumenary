import math

import pytest

import congruences_crt_solver as cs


@pytest.mark.parametrize("a,b", [(240, 46), (46, 240), (17, 0), (0, 5), (-12, 18), (35, 64)])
def test_ext_gcd_bezout(a, b):
    g, u, v = cs.ext_gcd(a, b)
    assert g == math.gcd(a, b)
    assert u * a + v * b == g


def test_inverse_mod():
    assert cs.inverse_mod(7, 26) == 15
    assert cs.inverse_mod(17, 43) == 38
    assert cs.inverse_mod(6, 9) is None
    for n in range(2, 40):
        for a in range(n):
            inv = cs.inverse_mod(a, n)
            if math.gcd(a, n) == 1:
                assert a * inv % n == 1
            else:
                assert inv is None


def test_solve_linear_matches_brute_force():
    for n in range(1, 25):
        for a in range(n):
            for b in range(n):
                brute = [x for x in range(n) if (a * x - b) % n == 0]
                assert sorted(cs.solve_linear(a, b, n)) == brute
                if brute:
                    assert len(brute) == math.gcd(a, n)


def test_crt_examples():
    assert cs.crt([2, 3, 2], [3, 5, 7]) == (23, 105)
    assert cs.crt([2, 3, 4], [5, 7, 9]) == (157, 315)
    with pytest.raises(ValueError):
        cs.crt([1, 2], [4, 6])


def test_crt_bijection_iff_coprime():
    assert cs.crt_is_bijection([3, 5, 7])
    assert not cs.crt_is_bijection([4, 6])
    for m in range(1, 13):
        for n in range(1, 13):
            assert cs.crt_is_bijection([m, n]) == (math.gcd(m, n) == 1)


def test_consistency_rule():
    # Solvable exactly when r1 = r2 (mod gcd(m1, m2)).
    for r1 in range(4):
        for r2 in range(6):
            assert cs.consistent(r1, 4, r2, 6) == ((r1 - r2) % 2 == 0)
