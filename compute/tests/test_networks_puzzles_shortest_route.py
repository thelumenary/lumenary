import networks_puzzles_shortest_route as sr


def test_neighbours_are_symmetric():
    near = sr.neighbours(sr.ROADS)
    for a, nbrs in near.items():
        for b, km in nbrs.items():
            assert near[b][a] == km
    assert set(near) == {"Home", "Well", "School", "Bridge", "Market"}


def test_all_routes_listed():
    routes = sr.all_routes(sr.ROADS, "Home", "Market")
    assert len(routes) == 4
    for r in routes:
        assert r[0] == "Home" and r[-1] == "Market"
        assert len(set(r)) == len(r)
    assert ["Home", "Well", "Market"] in routes


def test_fewest_roads_is_not_shortest():
    routes = sr.all_routes(sr.ROADS, "Home", "Market")
    fewest = min(routes, key=len)
    shortest = min(routes, key=lambda r: sr.route_length(sr.ROADS, r))
    assert sr.route_length(sr.ROADS, fewest) == 13
    assert sr.route_length(sr.ROADS, shortest) == 9
    assert len(fewest) < len(shortest)


def test_dijkstra_matches_exhaustive_search():
    best, settled = sr.dijkstra(sr.ROADS, "Home")
    assert best == {"Home": 0, "School": 2, "Bridge": 5, "Well": 7, "Market": 9}
    assert settled[0] == "Home" and settled[-1] == "Market"
    for place in best:
        if place == "Home":
            continue
        lengths = [sr.route_length(sr.ROADS, r) for r in sr.all_routes(sr.ROADS, "Home", place)]
        assert best[place] == min(lengths)


def test_dijkstra_settles_in_increasing_distance():
    best, settled = sr.dijkstra(sr.ROADS, "Market")
    dists = [best[p] for p in settled]
    assert dists == sorted(dists)


def test_route_length_of_single_place_is_zero():
    assert sr.route_length(sr.ROADS, ["Home"]) == 0
