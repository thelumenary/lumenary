import pytest

import riemann_surfaces_riemann_hurwitz as rh


@pytest.mark.parametrize(
    "num, den, degree",
    [([1, 0, -3, 0], [1], 3), ([1, 0, 0, 0, 0], [1], 4), ([1, 0, 1], [1, -2], 2),
     ([1, 0, 0, -1], [1, 0, 3], 3), ([1, 0, 0, 0, 1, 0], [1], 5)],
)
def test_riemann_hurwitz_for_rational_maps(num, den, degree):
    assert -2 == degree * (-2) + rh.total_ramification(num, den)


def test_local_degrees():
    assert rh.local_degree([1, 0, 0, 0, 0], [1], 0) == 4
    assert rh.local_degree([1, 0, -3, 0], [1], 1) == 2
    assert rh.local_degree([1, 0, -3, 0], [1], 0.5) == 1


def test_genus_formulas():
    assert [rh.hyperelliptic_genus(d) for d in range(1, 9)] == [0, 0, 1, 1, 2, 2, 3, 3]
    for d in range(1, 9):
        assert rh.fermat_genus(d) == (d - 1) * (d - 2) // 2
    with pytest.raises(ValueError):
        rh.riemann_hurwitz_genus(2, 0, 3)  # an odd number of branch points is impossible


def test_monodromy_of_square_roots():
    assert rh.continue_sqrt(lambda z: z, 0, 1.0) == pytest.approx(-1)
    assert rh.continue_sqrt(lambda z: z, 0, 1.0, turns=2) == pytest.approx(1)
    assert rh.continue_sqrt(lambda z: z, 3, 1.0) == pytest.approx(1)  # loop misses 0
    f = lambda z: z**3 - z
    assert rh.continue_sqrt(f, 1, 0.5) == pytest.approx(-1)
    assert rh.continue_sqrt(f, 0.5, 0.8) == pytest.approx(1)
