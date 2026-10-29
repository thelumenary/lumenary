import pytest

import limits_colimits_padic as lp


def test_fraction_towers():
    assert lp.tower_of_fraction(-1, 1, 5, 3) == [4, 24, 124]
    assert lp.tower_of_fraction(1, 3, 2, 5) == [1, 3, 3, 11, 11]
    t = lp.tower_of_fraction(2, 7, 3, 6)
    assert all((7 * x - 2) % 3 ** (n + 1) == 0 for n, x in enumerate(t))
    with pytest.raises(ValueError):
        lp.tower_of_fraction(1, 5, 5, 3)


def test_compatibility_detects_bad_towers():
    assert lp.is_compatible([1, 6, 31], 5)
    assert not lp.is_compatible([1, 2, 3], 5)
    assert lp.is_compatible([3], 7)


def test_hensel_lifting_gives_compatible_roots():
    for x1 in (2, 3):
        t = lp.hensel_sqrt(-1, 5, x1, 7)
        assert lp.is_compatible(t, 5)
        assert all((x * x + 1) % 5 ** (n + 1) == 0 for n, x in enumerate(t))
    with pytest.raises(ValueError):
        lp.hensel_sqrt(2, 5, 1, 3)


def test_root_counts():
    assert lp.roots_mod(-1, 5) == [2, 3]
    assert [len(lp.roots_mod(-1, 5 ** n)) for n in range(1, 5)] == [2, 2, 2, 2]
    assert lp.roots_mod(2, 125) == []
    # Over Z_2, x^2 = 1 has more roots mod 8 than mod 2: Hensel needs 2x invertible.
    assert len(lp.roots_mod(1, 8)) == 4


def test_levelwise_arithmetic():
    i5 = lp.hensel_sqrt(-1, 5, 2, 5)
    assert lp.levelwise(lambda x, y: x * y, i5, i5, 5) == lp.tower_of_fraction(-1, 1, 5, 5)
    s = lp.levelwise(lambda x, y: x + y, [1, 1, 1], [1, 3, 7], 2)
    assert s == [0, 0, 0]  # 1 + (-1) = 0 at every level
