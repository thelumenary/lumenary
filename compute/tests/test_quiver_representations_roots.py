from fractions import Fraction

import quiver_representations_roots as qr

EXPECTED = {"A4 (linear)": 10, "A4 (zigzag)": 10, "D4": 12, "D5": 20,
            "E6": 36, "E7": 63, "E8": 120}


def test_tits_form_values():
    d4 = qr.QUIVERS["D4"][1]
    assert qr.tits_form((1, 2, 1, 1), d4) == 1  # highest root of D4
    assert qr.tits_form((0, 0, 0, 0), d4) == 0
    assert qr.tits_form((1, 1), qr.KRONECKER[1]) == 0
    assert qr.tits_form((1, 2), qr.KRONECKER[1]) == 1


def test_reflections_preserve_tits_form():
    for n, arrows in qr.QUIVERS.values():
        x = tuple(range(1, n + 1))
        for i in range(n):
            assert qr.tits_form(qr.reflect(x, i, arrows), arrows) == \
                qr.tits_form(x, arrows)
            assert qr.reflect(qr.reflect(x, i, arrows), i, arrows) == x


def test_root_counts_match_lie_theory():
    for name, (n, arrows) in qr.QUIVERS.items():
        assert len(qr.roots_by_reflection(n, arrows)) == EXPECTED[name]


def test_brute_force_agrees_on_small_types():
    for name in ["A4 (linear)", "D4", "D5", "E6"]:
        n, arrows = qr.QUIVERS[name]
        refl = qr.roots_by_reflection(n, arrows)
        bound = max(max(x) for x in refl)
        assert qr.roots_by_brute_force(n, arrows, bound) == refl
        # A larger box finds nothing new: the form is positive definite.
        if n <= 5:
            assert qr.roots_by_brute_force(n, arrows, bound + 1) == refl


def test_knitting_finds_each_root_once():
    for name, (n, arrows) in qr.QUIVERS.items():
        knitted = qr.knit(n, arrows)
        assert len(knitted) == len(set(knitted)) == EXPECTED[name]
        assert set(knitted) == qr.roots_by_reflection(n, arrows)


def test_root_count_independent_of_orientation():
    n = 4
    a = qr.roots_by_reflection(n, [(0, 1), (1, 2), (2, 3)])
    b = qr.roots_by_reflection(n, [(1, 0), (1, 2), (3, 2)])
    assert a == b


def test_coxeter_on_a2():
    cinv = qr.coxeter_inverse(2, [(0, 1)])
    assert cinv == [[Fraction(-1), Fraction(1)], [Fraction(-1), Fraction(0)]]
    assert qr.projective_dims(2, [(0, 1)]) == [(1, 1), (0, 1)]
    assert sorted(qr.knit(2, [(0, 1)])) == [(0, 1), (1, 0), (1, 1)]


def test_kronecker_is_infinite_type():
    n, arrows = qr.KRONECKER
    pre = qr.knit(n, arrows, max_steps=10)
    assert len(pre) == 20  # never stops: the cap is reached on both orbits
    assert all(qr.tits_form(x, arrows) == 1 for x in pre)
    assert all(abs(x[0] - x[1]) == 1 for x in pre)
    for p in (2, 3, 5, 7, 11):
        assert qr.kronecker_family_count(p) == p + 1
