import itertools

import graph_basics_euler as ge


def test_degrees_and_handshake():
    deg = ge.degrees(4, ge.KONIGSBERG)
    assert deg == [5, 3, 3, 3]
    assert sum(deg) == 2 * len(ge.KONIGSBERG)


def test_connectivity():
    assert ge.is_connected(3, [(0, 1), (1, 2)])
    assert not ge.is_connected(3, [(0, 1)])
    assert ge.is_connected(1, [])


def test_trail_search_small_cases():
    triangle = [(0, 1), (1, 2), (2, 0)]
    path = [(0, 1), (1, 2)]
    assert ge.euler_trail_exists(3, triangle, True)
    assert not ge.euler_trail_exists(3, path, True)
    assert ge.euler_trail_exists(3, path, False)
    assert not ge.euler_trail_exists(4, ge.KONIGSBERG, False)
    # one extra bridge between two odd banks gives an Euler trail
    assert ge.euler_trail_exists(4, ge.KONIGSBERG + [(1, 2)], False)


def test_hierholzer_builds_euler_circuits():
    for n in (3, 5, 7):
        kn = list(itertools.combinations(range(n), 2))
        circuit = ge.hierholzer(n, kn)
        steps = {frozenset(e) for e in zip(circuit, circuit[1:])}
        assert circuit[0] == circuit[-1] == 0
        assert len(circuit) - 1 == len(kn)
        assert steps == {frozenset(e) for e in kn}


def test_euler_criterion_on_all_small_graphs():
    assert ge.check_all_graphs(4) == (38, 0)
    assert ge.check_all_graphs(5) == (728, 0)
