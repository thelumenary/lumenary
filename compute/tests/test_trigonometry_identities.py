import math

import pytest
import sympy

import trigonometry_identities as ti


def test_true_identities_hold_to_rounding():
    pairs = ti.random_pairs(500, 1)
    for name, identity in ti.IDENTITIES.items():
        err = ti.max_error(identity, pairs)
        if "false" in name:
            assert err > 1.0
        else:
            assert err < 1e-12


def test_false_rule_counterexample():
    lhs, rhs = ti.IDENTITIES["sin(a+b) = sin a + sin b  (false!)"](math.pi / 2, math.pi / 2)
    assert lhs == pytest.approx(0, abs=1e-15)
    assert rhs == pytest.approx(2)


def test_random_pairs_seeded_and_in_range():
    p1, p2 = ti.random_pairs(50, 3), ti.random_pairs(50, 3)
    assert p1 == p2 and len(p1) == 50
    assert all(abs(a) <= 2 * math.pi and abs(b) <= 2 * math.pi for a, b in p1)


def test_triangle_and_laws_on_a_3_4_5_triangle():
    sides, angles = ti.triangle((0, 0), (4, 0), (0, 3))
    assert sorted(sides) == pytest.approx([3, 4, 5])
    assert sum(angles) == pytest.approx(math.pi)
    assert angles[0] == pytest.approx(math.pi / 2)  # right angle at (0, 0)
    e_cos, e_sin = ti.law_errors(sides, angles)
    assert e_cos < 1e-12 and e_sin < 1e-12


def test_law_errors_detect_wrong_angles():
    sides, (pa, pb, pc) = ti.triangle((0, 0), (4, 0), (1, 3))
    e_cos, e_sin = ti.law_errors(sides, (pa, pb, pc + 0.1))
    assert e_cos > 1e-3 and e_sin > 1e-3


def test_symbolic_difference():
    a, b = sympy.symbols("a b")
    assert ti.symbolic_difference(sympy.sin(a + b),
                                  sympy.sin(a) * sympy.cos(b) + sympy.cos(a) * sympy.sin(b)) == 0
    assert ti.symbolic_difference(sympy.sin(2 * a), 2 * sympy.sin(a) * sympy.cos(a)) == 0
    assert ti.symbolic_difference(sympy.sin(a + b), sympy.sin(a) + sympy.sin(b)) != 0
