import itertools
import random

import pytest

import conic_sections_classify as cc


def test_named_examples():
    expected = ["circle", "ellipse", "parabola", "hyperbola", "empty", "point",
                "two crossing lines", "two parallel lines", "one line", "empty"]
    assert [cc.classify(*c) for _, c in cc.EXAMPLES] == expected


def test_det3():
    assert cc.det3([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) == 1
    assert cc.det3([[2, 0, -2], [0, 2, 4], [-2, 4, 2]]) == -32
    assert cc.det3([[1, 2, 3], [4, 5, 6], [7, 8, 9]]) == 0


def test_rejects_first_degree_equations():
    with pytest.raises(ValueError):
        cc.classify(0, 0, 0, 1, 2, 3)


def rotate90(A, B, C, D, E, F):
    """Coefficients after substituting (x, y) -> (-y, x)."""
    return (C, -B, A, E, -D, F)


def translate(A, B, C, D, E, F, h, k):
    """Coefficients after substituting (x, y) -> (x + h, y + k)."""
    return (A, B, C,
            2 * A * h + B * k + D,
            B * h + 2 * C * k + E,
            A * h * h + B * h * k + C * k * k + D * h + E * k + F)


def test_type_is_invariant_under_motions_and_scaling():
    rng = random.Random(0)
    for _ in range(2000):
        c = tuple(rng.randint(-3, 3) for _ in range(6))
        if c[:3] == (0, 0, 0):
            continue
        kind = cc.classify(*c)
        assert cc.classify(*rotate90(*c)) == kind
        assert cc.classify(*translate(*c, rng.randint(-3, 3), rng.randint(-3, 3))) == kind
        assert cc.classify(*(-x for x in c)) == kind
        assert cc.classify(*(2 * x for x in c)) == kind


def test_ellipse_and_empty_are_bounded_hyperbola_is_not():
    """For C != 0, solving for y needs (B^2-4AC)x^2 + ... >= 0."""
    for c in itertools.product(range(-2, 3), repeat=6):
        A, B, C, D, E, F = c
        if C == 0 or c[:3] == (0, 0, 0):
            continue
        kind = cc.classify(*c)
        far = 10 ** 6
        disc_y = (B * far + E) ** 2 - 4 * C * (A * far * far + D * far + F)
        if kind in ("ellipse", "circle", "empty", "point"):
            assert disc_y < 0  # no real y far away: the set is bounded
        if kind in ("hyperbola", "two crossing lines"):
            assert disc_y > 0  # real points arbitrarily far away
