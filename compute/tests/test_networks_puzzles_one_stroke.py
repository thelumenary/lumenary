import itertools

import networks_puzzles_one_stroke as ns


def uses_each_line_once(route, lines):
    """Check that consecutive dots of the route use every line exactly once."""
    walked = sorted("".join(sorted(route[i:i + 2])) for i in range(len(route) - 1))
    return walked == sorted("".join(sorted(line)) for line in lines)


def test_degrees_and_handshake():
    for lines in ns.FIGURES.values():
        deg = ns.degrees(lines)
        assert sum(deg.values()) == 2 * len(lines)
    assert ns.degrees(ns.FIGURES["Konigsberg bridges"]) == {"E": 3, "I": 5, "N": 3, "S": 3}
    assert ns.degrees(ns.FIGURES["house"]) == {"A": 3, "B": 3, "C": 4, "D": 4, "E": 2}


def test_number_of_odd_dots_is_even():
    for lines in ns.FIGURES.values():
        assert len(ns.odd_dots(lines)) % 2 == 0


def test_found_routes_are_genuine_and_end_at_odd_dots():
    for lines in ns.FIGURES.values():
        route = ns.find_one_stroke(lines)
        if route is None:
            continue
        assert uses_each_line_once(route, lines)
        odd = ns.odd_dots(lines)
        if odd:
            assert {route[0], route[-1]} == set(odd)
        else:
            assert route[0] == route[-1]


def test_impossible_figures():
    for name in ["envelope (2 diagonals)", "Konigsberg bridges", "two triangles apart"]:
        assert ns.find_one_stroke(ns.FIGURES[name]) is None


def test_connectedness():
    assert ns.is_connected(ns.FIGURES["house"])
    assert not ns.is_connected(ns.FIGURES["two triangles apart"])
    assert ns.is_connected([])


def test_rule_agrees_with_search_on_all_small_simple_graphs():
    # Every simple graph on 4 labelled dots whose lines touch all 4 dots.
    pairs = ["AB", "AC", "AD", "BC", "BD", "CD"]
    checked = 0
    for k in range(1, len(pairs) + 1):
        for lines in itertools.combinations(pairs, k):
            if len(ns.dots(list(lines))) < 4:
                continue
            checked += 1
            rule = ns.euler_rule_says_yes(list(lines))
            assert rule == (ns.find_one_stroke(list(lines)) is not None)
    assert checked > 30
