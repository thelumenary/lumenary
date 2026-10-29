from math import comb

import pytest

import complex_kahler_geometry_hodge_numbers as hn


def test_bounded_compositions():
    # coefficients of (1 + t + t^2)^4: 1, 4, 10, 16, 19, 16, 10, 4, 1
    assert [hn.bounded_compositions(k, 4, 2) for k in range(9)] == [
        1, 4, 10, 16, 19, 16, 10, 4, 1]
    assert hn.bounded_compositions(-1, 3, 5) == 0
    assert hn.bounded_compositions(5, 5, 3) == 101
    # without an effective cap it is stars and bars
    assert hn.bounded_compositions(6, 3, 6) == comb(8, 2)


@pytest.mark.parametrize("d", [3, 4, 5, 6, 7])
def test_plane_curves_have_the_genus_formula(d):
    h = hn.hodge_diamond(1, d)
    genus = (d - 1) * (d - 2) // 2
    assert h[(1, 0)] == h[(0, 1)] == genus
    assert hn.euler_from_hodge(h) == 2 - 2 * genus


def test_k3_and_quintic():
    k3 = hn.hodge_diamond(2, 4)
    assert (k3[(2, 0)], k3[(1, 1)], k3[(0, 2)]) == (1, 20, 1)
    assert hn.betti(k3, 2) == [1, 0, 22, 0, 1]
    quintic = hn.hodge_diamond(3, 5)
    assert hn.primitive_middle(3, 5) == [1, 101, 101, 1]
    assert quintic[(1, 1)] == quintic[(2, 2)] == 1
    assert hn.betti(quintic, 3) == [1, 0, 1, 204, 1, 0, 1]
    assert hn.euler_from_hodge(quintic) == -200


@pytest.mark.parametrize("n,d", [(1, 3), (2, 3), (2, 5), (3, 3), (3, 4),
                                 (3, 5), (4, 3), (4, 6)])
def test_two_euler_characteristics_agree(n, d):
    h = hn.hodge_diamond(n, d)
    assert hn.euler_from_hodge(h) == hn.euler_from_chern(n, d)
    assert hn.symmetric(h, n)
    assert all(b % 2 == 0 for b in hn.betti(h, n)[1::2])


def test_cubic_surface_is_rational():
    # a cubic surface is P^2 blown up in 6 points: b2 = 7, h^{2,0} = 0
    h = hn.hodge_diamond(2, 3)
    assert h[(2, 0)] == 0
    assert hn.betti(h, 2)[2] == 7


def test_diamond_lines_shape():
    lines = hn.diamond_lines(hn.hodge_diamond(2, 4), 2)
    assert len(lines) == 5
    assert "20" in lines[2]
    assert all(line == line.rstrip() for line in lines)
