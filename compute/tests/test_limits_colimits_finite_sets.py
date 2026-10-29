from itertools import product

import limits_colimits_finite_sets as lf


def cospan():
    A, B, C = range(4), range(3), range(2)
    return ({"A": A, "B": B, "C": C},
            [("A", "C", {a: a % 2 for a in A}), ("B", "C", {b: (b + 1) % 2 for b in B})])


def test_pullback_matches_formula():
    obj, arr = cospan()
    fam = lf.sections(obj, arr)
    direct = [(a, b) for a, b in product(range(4), range(3)) if a % 2 == (b + 1) % 2]
    assert sorted((x["A"], x["B"]) for x in fam) == sorted(direct)
    assert fam == lf.limit_via_equaliser(obj, arr)


def test_equaliser_and_limit_agree_on_random_like_diagrams():
    obj = {"X": range(5), "Y": range(4)}
    for k in range(4):
        arr = [("X", "Y", {x: (x * x + k) % 4 for x in range(5)}),
               ("X", "Y", {x: (3 * x) % 4 for x in range(5)})]
        assert lf.sections(obj, arr) == lf.limit_via_equaliser(obj, arr)


def test_empty_diagram_and_product():
    # No arrows: the limit is the product.
    obj = {"A": range(2), "B": range(3)}
    assert len(lf.sections(obj, [])) == 6
    assert len(lf.limit_via_equaliser(obj, [])) == 6


def test_colimits():
    span = {"K": range(2), "P": range(3), "Q": range(4)}
    arrows = [("K", "P", {0: 0, 1: 2}), ("K", "Q", {0: 0, 1: 3})]
    assert len(lf.colimit_classes(span, arrows)) == 5
    # No arrows: the colimit is the disjoint union.
    assert len(lf.colimit_classes({"A": range(2), "B": range(3)}, [])) == 5
    pair = {"X": range(6), "Y": range(3)}
    arrows = [("X", "Y", {x: x % 3 for x in range(6)}),
              ("X", "Y", {x: (2 * x) % 3 for x in range(6)})]
    classes = lf.colimit_classes(pair, arrows)
    assert len(classes) == 2
    assert any(("Y", 1) in c and ("Y", 2) in c for c in classes)


def test_reduced_word_counts():
    assert lf.reduced_words(3) == [1, 3, 4, 6]
    words = lf.reduced_words(10)
    assert all(words[n + 2] == 2 * words[n] for n in range(1, 9))
