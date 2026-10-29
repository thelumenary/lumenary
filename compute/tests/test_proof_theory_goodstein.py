import pytest

import proof_theory_goodstein as gs


def test_hereditary_base_round_trip():
    for base in [2, 3, 7]:
        for n in list(range(200)) + [10**12 + 3]:
            assert gs.evaluate(gs.hereditary(n, base), base) == n
    with pytest.raises(ValueError):
        gs.hereditary(5, 1)


def test_bump_examples():
    # 4 = 2^2 becomes 3^3 = 27; 19 = 2^(2^2) + 2 + 1 becomes 3^(3^3) + 3 + 1.
    assert gs.bump(4, 2) == 27
    assert gs.bump(19, 2) == 3 ** 27 + 4
    assert gs.bump(0, 5) == 0


def test_known_goodstein_terms():
    assert [n for n, _ in gs.goodstein(3, 10)] == [3, 3, 3, 2, 1, 0]
    assert [n for n, _ in gs.goodstein(2, 10)] == [2, 2, 1, 0]
    assert [n for n, _ in gs.goodstein(4, 9)] == [4, 26, 41, 60, 83, 109, 139, 173, 211, 253]
    assert gs.goodstein(4, 3)[-1] == (60, 5)


def test_ordinals_compare_like_cantor_normal_forms():
    omega = ((((), 1),), 1)  # one term w^1 * 1
    one = ((), 1)
    w = (omega,)
    w_plus_1 = (omega, one)
    w_squared = (((((), 2),), 1),)
    assert () < (one,) < w < w_plus_1 < w_squared
    assert gs.ordinal(3, 2) == w_plus_1
    assert gs.show(gs.ordinal(4, 2)) == "w^w"
    assert gs.show(gs.ordinal(26, 3)) == "w^2*2 + w*2 + 2"


def test_ordinals_strictly_decrease():
    for start, steps in [(3, 10), (4, 500), (5, 100), (6, 100)]:
        assert gs.strictly_decreasing(gs.goodstein(start, steps))
    assert not gs.strictly_decreasing([(3, 3), (3, 2)])
