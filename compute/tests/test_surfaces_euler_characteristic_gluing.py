import pytest

import surfaces_euler_characteristic_gluing as ex


@pytest.mark.parametrize(
    "word, v, chi, orientable, name",
    [
        ("aA", 2, 2, True, "sphere"),
        ("abAB", 1, 0, True, "torus"),
        ("abAb", 1, 0, False, "Klein bottle"),
        ("abab", 2, 1, False, "projective plane"),
        ("aa", 1, 1, False, "projective plane"),
        ("aabb", 1, 0, False, "Klein bottle"),
        ("abcABC", 2, 0, True, "torus"),
        ("abABcdCD", 1, -2, True, "orientable, genus 2"),
        ("aabbcc", 1, -1, False, "sum of 3 projective planes"),
    ],
)
def test_classic_words(word, v, chi, orientable, name):
    assert ex.vertex_count(word) == v
    assert ex.euler_characteristic(word) == chi
    assert ex.is_orientable(word) == orientable
    assert ex.name(chi, orientable) == name


def test_sphere_words_and_relabelling():
    # a b B A is a sphere (folded square); relabelling letters changes nothing.
    assert ex.euler_characteristic("abBA") == 2
    assert ex.euler_characteristic("xyYX") == 2
    # Cyclic rotation of the word describes the same surface.
    assert ex.euler_characteristic("bABa") == ex.euler_characteristic("abAB") == 0


def test_torus_plus_projective_plane_is_three_projective_planes():
    w1, w2 = "abABcc", "aabbcc"
    assert ex.euler_characteristic(w1) == ex.euler_characteristic(w2) == -1
    assert not ex.is_orientable(w1) and not ex.is_orientable(w2)


def test_pairings_count_is_double_factorial():
    for n, expected in [(1, 1), (2, 3), (3, 15), (4, 105)]:
        assert sum(1 for _ in ex.pairings(list(range(2 * n)))) == expected


def test_genus_census_matches_harer_zagier():
    assert ex.genus_census(3) == {0: 5, 1: 10}
    assert ex.genus_census(4) == {0: 14, 1: 70, 2: 21}
    assert ex.genus_census(5) == {0: 42, 1: 420, 2: 483}
    for n in range(1, 6):
        assert ex.genus_census(n)[0] == ex.catalan(n)


def test_chi_parity_and_bounds_for_orientable_words():
    # For an orientable one-polygon word with n letters, chi is even and >= 2 - n.
    for n in range(1, 5):
        for g, _ in ex.genus_census(n).items():
            chi = 2 - 2 * g
            assert chi % 2 == 0 and chi >= 2 - n
