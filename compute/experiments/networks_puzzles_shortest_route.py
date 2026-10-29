"""Shortest routes on a small road map: list every route, then be clever.

Wanjiru cycles from home to the market. The map has five places and six
roads, each marked with its length in kilometres. First the program lists
*every* route that never visits a place twice, with its number of roads and
its length: an exhaustive check. Then it runs Dijkstra's method, which finds
the shortest distance from home to every place without listing all routes,
by always settling the nearest place not yet settled.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "networks_puzzles_shortest_route",
    "title": "Fewest roads or fewest kilometres? Shortest routes",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["networks-puzzles"],
    "summary": (
        "Lists every route from home to the market on a five-place road map "
        "with its number of roads and its length, showing that the route "
        "with fewest roads (13 km) is not the shortest (9 km). Dijkstra's "
        "method finds the same 9 km without listing every route. Exact for "
        "this map only."
    ),
    "packages": [],
}

#: (place, place, kilometres)
ROADS = [
    ("Home", "Well", 7),
    ("Well", "Market", 6),
    ("Home", "School", 2),
    ("School", "Bridge", 3),
    ("Bridge", "Market", 4),
    ("Well", "Bridge", 2),
]


def neighbours(roads):
    """Return {place: {neighbour: km}} for roads that work in both directions."""
    near = {}
    for a, b, km in roads:
        near.setdefault(a, {})[b] = km
        near.setdefault(b, {})[a] = km
    return near


def all_routes(roads, start, goal):
    """Every route from start to goal that never visits a place twice."""
    near = neighbours(roads)
    found = []

    def extend(route):
        here = route[-1]
        if here == goal:
            found.append(route)
            return
        for nxt in sorted(near[here]):
            if nxt not in route:
                extend(route + [nxt])

    extend([start])
    return found


def route_length(roads, route):
    """Total kilometres along a route (a list of places)."""
    near = neighbours(roads)
    return sum(near[a][b] for a, b in zip(route, route[1:]))


def dijkstra(roads, start):
    """Shortest distance from start to every place, and the settling order.

    Repeatedly settle the unsettled place with the smallest known distance,
    then update the distances of its neighbours.
    """
    near = neighbours(roads)
    best = {start: 0}
    settled = []
    while len(settled) < len(near):
        here = min((d, p) for p, d in best.items() if p not in settled)[1]
        settled.append(here)
        for nxt, km in near[here].items():
            if nxt not in best or best[here] + km < best[nxt]:
                best[nxt] = best[here] + km
    return best, settled


def main():
    routes = all_routes(ROADS, "Home", "Market")
    print("Every route from Home to Market that never repeats a place:")
    for route in sorted(routes, key=lambda r: (len(r), route_length(ROADS, r))):
        roads_used = len(route) - 1
        km = route_length(ROADS, route)
        print(f"  {' - '.join(route):<38} {roads_used} roads  {km:>2} km")
    fewest = min(routes, key=len)
    shortest = min(routes, key=lambda r: route_length(ROADS, r))
    print(f"Fewest roads:   {' - '.join(fewest)}"
          f" ({route_length(ROADS, fewest)} km)")
    print(f"Shortest route: {' - '.join(shortest)}"
          f" ({route_length(ROADS, shortest)} km)")
    print()
    best, settled = dijkstra(ROADS, "Home")
    print("Dijkstra's method settles the nearest unsettled place each time:")
    for place in settled:
        print(f"  {place:<7} {best[place]:>2} km from Home")
    print()
    print(textwrap.fill(
        "Epistemic status: exact. All four routes on this small map were "
        "listed, so the 9 km route is certainly the shortest here, and "
        "Dijkstra's method agrees. That the method always gives the shortest "
        "distance (when no road has negative length) is a theorem proved in "
        "later courses; this run checks one map only.",
        width=78,
    ))


if __name__ == "__main__":
    main()
