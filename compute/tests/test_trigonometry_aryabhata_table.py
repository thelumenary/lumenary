import math

import pytest

import trigonometry_aryabhata_table as at


def test_half_angle_values():
    s, c = at.half_angle(0.5, math.sqrt(3) / 2)  # 30 deg -> 15 deg
    assert s == pytest.approx(math.sin(math.radians(15)))
    assert c == pytest.approx(math.cos(math.radians(15)))
    assert at.half_angle(0.0, -1.0) == pytest.approx((1.0, 0.0))  # 180 -> 90


def test_step_is_three_and_three_quarter_degrees():
    s, c = at.step_sine_and_cosine()
    assert s == pytest.approx(math.sin(math.radians(3.75)), abs=1e-15)
    assert s * s + c * c == pytest.approx(1.0)


def test_recurrence_matches_math_sin():
    table = at.sine_table(1.0, 48)
    assert len(table) == 49
    for n, value in enumerate(table):
        assert value == pytest.approx(math.sin(math.radians(3.75 * n)), abs=1e-12)


def test_aryabhata_data_and_cumulative_sums():
    assert len(at.ARYABHATA_DIFFERENCES) == 24
    assert at.cumulative([1, 2, 3]) == [1, 3, 6]
    entries = at.cumulative(at.ARYABHATA_DIFFERENCES)
    assert entries[-1] == at.RADIUS == 3438  # sin 90 deg = 1
    # Differences of sines shrink as the angle grows (sine is concave on [0, 90]).
    d = at.ARYABHATA_DIFFERENCES
    assert all(d[i] > d[i + 1] for i in range(23))


def test_ancient_table_is_within_one_unit():
    rebuilt = at.sine_table(at.RADIUS, 24)
    entries = at.cumulative(at.ARYABHATA_DIFFERENCES)
    gaps = [abs(a - r) for a, r in zip(entries, rebuilt[1:])]
    assert max(gaps) < 1
    assert sum(a == round(r) for a, r in zip(entries, rebuilt[1:])) == 19
