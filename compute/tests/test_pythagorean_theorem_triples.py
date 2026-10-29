import math

import pythagorean_theorem_triples as pt


def test_small_triples():
    assert pt.triples(20) == [(3, 4, 5), (6, 8, 10), (5, 12, 13), (9, 12, 15),
                              (8, 15, 17), (12, 16, 20)]
    for a, b, c in pt.triples(100):
        assert a * a + b * b == c * c and 0 < a < b < c <= 100


def test_counts_up_to_100():
    all_t = pt.triples(100)
    assert len(all_t) == 52
    assert len([t for t in all_t if pt.is_primitive(t)]) == 16


def test_euclid_formula():
    assert pt.euclid(2, 1) == (3, 4, 5)
    assert pt.euclid(3, 2) == (5, 12, 13)
    assert pt.euclid(4, 1) == (8, 15, 17)
    for m in range(2, 30):
        for n in range(1, m):
            a, b, c = pt.euclid(m, n)
            assert a * a + b * b == c * c


def test_euclid_gives_exactly_the_primitives():
    for limit in (30, 100, 300):
        prim = [t for t in pt.triples(limit) if pt.is_primitive(t)]
        assert pt.euclid_primitives(limit) == prim


def test_primitive_root_and_sixty():
    assert pt.primitive_root((6, 8, 10)) == (3, 4, 5)
    assert pt.primitive_root((5, 12, 13)) == (5, 12, 13)
    assert all(a * b * c % 60 == 0 for a, b, c in pt.triples(300))


def test_hypotenuse_counts():
    counts = pt.hypotenuse_counts(pt.triples(100))
    assert counts[5] == 1 and counts[25] == 2
    assert counts[65] == counts[85] == 4 == max(counts.values())
