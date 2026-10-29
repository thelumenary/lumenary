import pytest

import measurement_units_and_gaps as mu


def test_measure_whole_units_and_leftover():
    assert mu.measure(15, 3) == (5, 0)
    assert mu.measure(13, 5) == (2, 3)
    assert mu.measure(0, 5) == (0, 0)
    with pytest.raises(ValueError):
        mu.measure(10, 0)


def test_describe_is_honest():
    assert mu.describe(15, 5) == "exactly 3"
    assert mu.describe(7, 3) == "2 to 3"
    assert mu.describe(5, 12) == "less than 1"
    assert mu.describe(12, 12) == "exactly 1"


def test_smaller_unit_gives_bigger_or_equal_count_for_every_object():
    units = sorted(mu.UNITS.values())
    for cm in mu.OBJECTS.values():
        counts = [mu.measure(cm, u)[0] for u in units]
        assert counts == sorted(counts, reverse=True)
    assert mu.smaller_unit_never_smaller_count(30, 10)


def test_careful_measuring_counts_exactly():
    assert mu.clips_that_fit(15, 3, [0.0] * 10) == 5
    assert mu.clips_that_fit(14, 3, [0.0] * 10) == 4
    assert mu.clips_that_fit(2, 3, [0.0] * 10) == 0


def test_gaps_never_raise_and_overlaps_never_lower_the_count():
    careful = mu.clips_that_fit(15, 3, [0.0] * 20)
    gaps = mu.simulate(15, 3, 0.0, 1.0, 200, seed=7)
    overlaps = mu.simulate(15, 3, -1.0, 0.0, 200, seed=7)
    assert max(gaps) <= careful
    assert min(overlaps) >= careful
    assert sum(gaps.values()) == sum(overlaps.values()) == 200


def test_simulation_is_reproducible():
    assert mu.simulate(15, 3, 0.2, 1.0, 100, seed=1) == mu.simulate(15, 3, 0.2, 1.0, 100, seed=1)
