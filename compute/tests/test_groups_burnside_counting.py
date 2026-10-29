import pytest

import groups_burnside_counting as gb


def test_group_sizes():
    for n in range(1, 9):
        assert len(gb.cyclic_group(n)) == n
        assert len(gb.dihedral_group(n)) == (2 * n if n >= 3 else n)
    assert len(gb.cube_rotations()) == 24


@pytest.mark.parametrize("perm, cycles", [((0, 1, 2), 3), ((1, 2, 0), 1), ((1, 0, 2, 3), 3), ((1, 0, 3, 2), 2)])
def test_cycle_count(perm, cycles):
    assert gb.cycle_count(perm) == cycles


def test_known_necklace_and_bracelet_numbers():
    # OEIS A000031 and A000029 (binary necklaces and bracelets)
    necklaces = [2, 3, 4, 6, 8, 14, 20, 36]
    bracelets = [2, 3, 4, 6, 8, 13, 18, 30]
    for n in range(1, 9):
        assert gb.burnside(gb.cyclic_group(n), 2) == necklaces[n - 1]
        assert gb.burnside(gb.dihedral_group(n), 2) == bracelets[n - 1]


def test_burnside_matches_brute_force():
    for n in range(1, 7):
        for k in (1, 2, 3):
            for group in (gb.cyclic_group(n), gb.dihedral_group(n)):
                assert gb.burnside(group, k) == gb.brute_force(group, k)


def test_cube_colourings():
    cube = gb.cube_rotations()
    assert gb.burnside(cube, 2) == 10
    assert gb.burnside(cube, 3) == 57
    assert gb.brute_force(cube, 2) == 10


def test_one_colour_gives_one_orbit():
    assert gb.burnside(gb.dihedral_group(7), 1) == 1
