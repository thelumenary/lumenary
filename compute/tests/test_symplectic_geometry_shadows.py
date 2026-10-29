import math
import random

import pytest

import symplectic_geometry_shadows as sh

SQUEEZE = [[0.5, 0, 0, 0], [0, 0.5, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]
EYE = [[float(i == j) for j in range(4)] for i in range(4)]


def test_matrix_helpers():
    assert sh.matmul(EYE, SQUEEZE) == SQUEEZE
    assert sh.transpose([[1, 2], [3, 4]]) == [[1, 3], [2, 4]]
    assert sh.det4(EYE) == 1
    assert sh.det4(SQUEEZE) == pytest.approx(1.0)
    assert sh.det4([[2, 0, 0, 0], [0, 3, 0, 0], [0, 0, 1, 0], [1, 0, 0, 1]]) == 6


def test_omega_is_alternating_and_standard():
    u, v = [1, 2, 3, 4], [-1, 0, 5, 2]
    assert sh.omega(u, v) == -sh.omega(v, u)
    assert sh.omega(u, u) == 0
    assert sh.omega([1, 0, 0, 0], [0, 1, 0, 0]) == 1
    assert sh.omega([0, 0, 1, 0], [0, 0, 0, 1]) == 1


def test_elementary_maps_are_symplectic():
    rng = random.Random(7)
    for _ in range(200):
        assert sh.symplectic_defect(sh.elementary_symplectic(rng)) < 1e-12


def test_squeeze_is_volume_preserving_but_not_symplectic():
    assert sh.symplectic_defect(SQUEEZE) == pytest.approx(3.0)
    assert sh.shadow_area(SQUEEZE, 0, 1) == pytest.approx(math.pi / 4)
    assert sh.shadow_area(EYE, 0, 1) == pytest.approx(math.pi)


def test_symplectic_shadows_never_below_pi():
    rng = random.Random(11)
    for _ in range(500):
        a = sh.random_symplectic(rng)
        assert sh.symplectic_defect(a) < 1e-9
        assert sh.det4(a) == pytest.approx(1.0, abs=1e-6)
        assert sh.shadow_area(a, 0, 1) >= math.pi * (1 - 1e-9)
        assert sh.shadow_area(a, 2, 3) >= math.pi * (1 - 1e-9)


def test_lagrangian_shadow_can_be_small_for_symplectic_maps():
    eps = 0.1
    a = [[eps, 0, 0, 0], [0, 1 / eps, 0, 0], [0, 0, eps, 0], [0, 0, 0, 1 / eps]]
    assert sh.symplectic_defect(a) < 1e-12
    assert sh.shadow_area(a, 0, 2) == pytest.approx(math.pi * eps ** 2)
    assert sh.shadow_area(a, 0, 1) == pytest.approx(math.pi)


def test_random_volume_preserving_has_det_one():
    rng = random.Random(3)
    for _ in range(50):
        assert sh.det4(sh.random_volume_preserving(rng)) == pytest.approx(1.0)
