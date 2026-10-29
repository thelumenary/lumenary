import math

import pytest

import differential_topology_poincare_hopf as ph


@pytest.mark.parametrize("k", [-3, -1, 1, 2, 4])
def test_index_of_z_power(k):
    if k > 0:
        field = lambda z: z**k
    else:
        field = lambda z: z.conjugate() ** (-k)
    assert ph.index(field, 0) == k


def test_index_of_nonzero_point_is_zero():
    assert ph.index(lambda z: z * z - 1, 0.5j) == 0
    assert ph.index(lambda z: 1 + 0j, 0) == 0


def test_index_does_not_depend_on_small_radius():
    field = lambda z: z**2 * (z - 3)
    assert ph.index(field, 0, radius=1e-2) == ph.index(field, 0, radius=1e-4) == 2


def test_south_chart_formula():
    w = 0.3 + 0.4j
    assert ph.south_chart(lambda z: z)(w) == pytest.approx(-w)
    assert ph.south_chart(lambda z: 1 + 0j)(w) == pytest.approx(-w * w)


def test_sphere_indices_sum_to_two():
    for _, field, zeros, at_infinity in ph.SPHERE:
        total = sum(ph.index(field, z) for z in zeros)
        if at_infinity:
            total += ph.index(ph.south_chart(field), 0)
        else:
            assert abs(ph.south_chart(field)(0j + 1e-12)) > 0.5
        assert total == 2


def test_torus_indices_sum_to_zero():
    grad = ph.torus_gradient()
    points = [(0, 0), (0, math.pi), (math.pi, math.pi), (math.pi, 0)]
    indices = [ph.index(grad, complex(u, v)) for u, v in points]
    assert indices == [1, -1, -1, 1]
    assert sum(indices) == 0
