from fractions import Fraction
from itertools import product

import commutative_diagrams_intro_squares as cd


def test_around_zero_order():
    assert cd.around_zero(2) == [0, -1, 1, -2, 2]
    assert sorted(cd.around_zero(50)) == list(range(-50, 51))


def test_first_disagreement():
    xs = cd.around_zero(50)
    assert cd.first_disagreement(lambda x: 2 * x + 2, lambda x: 2 * (x + 1), xs) is None
    assert cd.first_disagreement(lambda x: 2 * (x + 1), lambda x: 2 * x + 1, xs) == 0
    # square and double agree at 0 and 2 only
    assert cd.first_disagreement(lambda x: x * x, lambda x: 2 * x, xs) == -1
    assert [x for x in xs if x * x == 2 * x] == [0, 2]


def test_add_counterexamples():
    vals = cd.around_zero(20)
    assert cd.add_counterexample(lambda x: 100 * x, vals) is None
    assert cd.add_counterexample(lambda x: -3 * x, vals) is None
    assert cd.add_counterexample(lambda x: x + 1, vals) == (0, 0)
    assert cd.add_counterexample(lambda x: x * x, vals) == (-1, -1)
    assert cd.add_counterexample(lambda x: Fraction(9, 5) * x + 32, vals) == (0, 0)
    # last digit preserves addition if the digits are added with wrap-around
    last = lambda x: x % 10  # noqa: E731
    assert cd.add_counterexample(last, range(100), add=lambda a, b: (a + b) % 10) is None
    assert cd.add_counterexample(last, range(100)) is not None


def test_additive_maps_mod_n_are_multiplications():
    for n in range(1, 7):
        maps = cd.additive_maps_mod(n)
        assert len(maps) == n
        assert sorted(maps) == sorted(tuple(m * x % n for x in range(n)) for m in range(n))


def test_square_commutes_on_tuples():
    ident, swap, zero = (0, 1), (1, 0), (0, 0)
    assert cd.square_commutes(swap, swap, ident, ident, (0, 1))
    assert not cd.square_commutes(swap, ident, ident, ident, (0, 1))
    assert cd.square_commutes(swap, zero, ident, zero, (0, 1))


def test_pasting_counts_and_independent_recount():
    both, outer, converse = cd.pasting_counts()
    assert both == outer  # pasting never fails
    assert converse > 0  # the converse does fail
    # Independent recount of "both squares commute" with dictionaries.
    maps = [dict(zip((0, 1), m)) for m in product((0, 1), repeat=2)]
    count = 0
    for f, g, f2, g2, a, b, c in product(maps, repeat=7):
        if all(b[f[x]] == f2[a[x]] and c[g[x]] == g2[b[x]] for x in (0, 1)):
            count += 1
    assert count == both == 1664
