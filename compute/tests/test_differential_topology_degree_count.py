import math

import pytest

import differential_topology_degree_count as dc


def test_lift_has_degree_three():
    for t in [0.0, 0.7, 2.0]:
        assert dc.lift(t + 2 * math.pi) - dc.lift(t) == pytest.approx(6 * math.pi)


def test_preimages_are_preimages():
    for y in dc.SAMPLE_VALUES:
        roots = dc.preimages(y)
        assert roots, "every value has a preimage"
        for t in roots:
            diff = (dc.lift(t) - y) / (2 * math.pi)
            assert diff == pytest.approx(round(diff), abs=1e-9)
            assert 0 <= t <= 2 * math.pi


@pytest.mark.parametrize("y", dc.SAMPLE_VALUES)
def test_signed_count_is_degree(y):
    roots = dc.preimages(y)
    assert dc.signed_count(roots) == 3
    assert len(roots) % 2 == 1  # unsigned count has the parity of the degree


def test_unsigned_count_varies():
    counts = {len(dc.preimages(y)) for y in dc.SAMPLE_VALUES}
    assert counts == {5, 7}


def test_critical_values_are_critical():
    s = math.acos(-3 / (2 * dc.WIGGLE)) / 2
    assert dc.lift_derivative(s) == pytest.approx(0, abs=1e-12)
    assert len(dc.critical_values()) == 4


def test_complex_preimages_and_critical_values():
    cubic = [1, 0, -3, 0]
    assert len(dc.complex_preimages(cubic, 1j)) == 3
    assert len(dc.complex_preimages(cubic, 2)) == 2
    crit = sorted(c.real for c in dc.critical_values_complex(cubic))
    assert crit == pytest.approx([-2, 2])
