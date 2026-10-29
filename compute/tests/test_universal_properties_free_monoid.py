from fractions import Fraction

import universal_properties_free_monoid as fm


def mat(w):
    return fm.evaluate(w, fm.GENERATORS, fm.matmul, fm.IDENTITY)


def test_matmul_and_identity():
    L, R = fm.GENERATORS["L"], fm.GENERATORS["R"]
    assert fm.matmul(fm.IDENTITY, L) == L == fm.matmul(L, fm.IDENTITY)
    assert fm.matmul(L, R) == ((1, 1), (1, 2))
    assert fm.matmul(R, L) == ((2, 1), (1, 1))


def test_evaluate_is_a_homomorphism():
    for v in fm.words(3):
        for w in fm.words(3):
            assert mat(v + w) == fm.matmul(mat(v), mat(w))
    assert mat("") == fm.IDENTITY
    # in (Z, +) the empty word goes to the unit 0
    assert fm.evaluate("", {"L": 1, "R": -1}, lambda x, y: x + y, 0) == 0


def test_words_counts():
    assert fm.words(0) == [""]
    assert len(fm.words(3)) == 15
    assert len(fm.words(10)) == 2047


def test_decode_inverts_and_rejects():
    for w in fm.words(8):
        assert fm.decode(mat(w)) == w
    # determinant 1 but negative entries: not in the monoid
    assert fm.decode(((0, -1), (1, 0))) is None
    assert fm.decode(((2, 0), (0, 1))) is None


def test_matrices_have_determinant_one_and_distinct():
    seen = set()
    for w in fm.words(9):
        (a, b), (c, d) = m = mat(w)
        assert a * d - b * c == 1
        assert m not in seen
        seen.add(m)


def test_stern_brocot_fractions():
    assert fm.fraction_of(mat("")) == 1
    assert fm.fraction_of(mat("R")) == 2
    assert fm.fraction_of(mat("L")) == Fraction(1, 2)
    assert fm.fraction_of(mat("RL")) == Fraction(3, 2)
    fracs = [fm.fraction_of(mat(w)) for w in fm.words(6)]
    assert len(set(fracs)) == len(fracs)
