import random
from fractions import Fraction

import projective_geometry_cross_ratio as pcr


def test_cross_ratio_matches_affine_formula():
    a, b, c, d = 2, 7, -3, 5
    expected = Fraction((a - c) * (b - d), (a - d) * (b - c))
    pts = [pcr.point(x) for x in (a, b, c, d)]
    assert pcr.cross_ratio(*pts) == expected


def test_cross_ratio_with_point_at_infinity():
    # (a, b; c, inf) = (a - c)/(b - c)
    pts = [pcr.point(5), pcr.point(1), pcr.point(0), pcr.INFINITY]
    assert pcr.cross_ratio(*pts) == 5


def test_mobius_maps_preserve_cross_ratio():
    rng = random.Random(1)
    for _ in range(50):
        quad = [pcr.point(x) for x in rng.sample(range(-30, 31), 4)]
        m = pcr.random_mobius(rng)
        images = [pcr.apply(m, p) for p in quad]
        assert pcr.cross_ratio(*images) == pcr.cross_ratio(*quad)


def test_inversion_sends_zero_to_infinity():
    m = ((Fraction(0), Fraction(1)), (Fraction(1), Fraction(0)))  # x -> 1/x
    assert pcr.affine(pcr.apply(m, pcr.point(0))) is None
    assert pcr.affine(pcr.apply(m, pcr.point(4))) == Fraction(1, 4)


def test_six_values_and_harmonic_case():
    lam = Fraction(3)
    vals = pcr.six_values(lam)
    expected = {lam, 1 / lam, 1 - lam, 1 / (1 - lam), (lam - 1) / lam,
                lam / (lam - 1)}
    assert set(vals) == expected and len(vals) == 6
    assert pcr.six_values(Fraction(-1)) == [Fraction(-1), Fraction(1, 2), 2]


def test_fourth_point_prediction():
    seen = [pcr.photo(x) for x in (0, 1, 2)]
    lam = pcr.cross_ratio(*[pcr.point(x) for x in (0, 1, 2, 3)])
    assert lam == Fraction(4, 3)
    assert pcr.fourth_point(*seen, lam) == pcr.photo(3) == Fraction(3, 5)
