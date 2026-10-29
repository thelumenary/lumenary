import itertools

import enriched_categories_shortest_paths as sp

INF = sp.INF


def test_min_plus_product_small():
    a = [[0, 1], [INF, 0]]
    b = [[0, 5], [2, 0]]
    assert sp.min_plus(a, b) == [[0, 1], [2, 0]]


def test_closure_is_shortest_path_distance():
    # A directed triangle 0 -> 1 -> 2 -> 0 with lengths 1, 2, 3.
    w = [[0, 1, INF], [INF, 0, 2], [3, INF, 0]]
    d = sp.closure(w)
    assert d == [[0, 1, 3], [5, 0, 2], [3, 4, 0]]
    assert sp.is_lawvere_metric(d)
    assert sp.min_plus(d, d) == d


def test_closure_of_town_is_a_lawvere_metric_and_asymmetric():
    w = sp.weight_matrix(sp.PLACES, sp.PATHS)
    d = sp.closure(w)
    assert sp.is_lawvere_metric(d)
    assert sp.asymmetric_pairs(d)
    n = len(d)
    assert all(d[i][j] <= w[i][j] for i in range(n) for j in range(n))
    # Ridge -> Market is faster via the Clinic and the School than directly.
    r, m = sp.PLACES.index("Ridge"), sp.PLACES.index("Market")
    assert w[r][m] == 20 and d[r][m] == 17


def test_is_lawvere_metric_rejects_violations():
    assert not sp.is_lawvere_metric([[0, 1], [1, 1]])            # d(y, y) != 0
    assert not sp.is_lawvere_metric([[0, 1, 5], [9, 0, 1], [9, 9, 0]])
    assert sp.is_lawvere_metric([[0, 0], [0, 0]])                # x != y, d = 0


def test_boolean_closure_is_reachability():
    a = [[True, True, False], [False, True, True], [False, False, True]]
    r = sp.closure(a, product=sp.or_and)
    assert r == [[True, True, True], [False, True, True], [False, False, True]]


def test_hausdorff_distance_is_a_lawvere_metric_on_subsets():
    d = sp.closure([[0, 1, INF], [INF, 0, 2], [3, INF, 0]])
    subsets = [s for k in range(1, 4) for s in itertools.combinations(range(3), k)]
    h = [[sp.hausdorff(d, s, t) for t in subsets] for s in subsets]
    assert sp.is_lawvere_metric(h)
    assert sp.hausdorff(d, (0,), (0, 1)) == 0      # a subset is "inside"
    assert sp.hausdorff(d, (0, 1), (0,)) == 5
