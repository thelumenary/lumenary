"""Reading a distance-time graph by computer: rates, averages and a trap.

A cyclist's trip to market and back is given as a table of (time, distance
from home). The experiment computes the average rate of change on each
segment of the graph and says whether the distance is increasing, constant or
decreasing there; checks that the rate over a longer stretch is the
length-weighted average of the rates of its pieces; contrasts the average
rate of change of distance-from-home (zero for a round trip) with the
average speed; and computes round-trip average speeds, which are never more
than the mean of the two speeds. All arithmetic is exact (fractions).
"""

from fractions import Fraction as F

EXPERIMENT = {
    "id": "graphs_of_change_journey",
    "title": "A journey graph: segment rates, averages and round trips",
    "evidence": ["exact"],
    "lessons": ["graphs-of-change"],
    "summary": (
        "Computes exact average rates of change on each segment of a cycling "
        "journey's distance-time table, classifies each segment as increasing, "
        "constant or decreasing, verifies the weighted-average rule for "
        "combining intervals, contrasts zero net change with the distance "
        "actually ridden, and compares round-trip average speeds with the mean "
        "of the two speeds."
    ),
    "packages": [],
}

#: (minutes since leaving home, km from home): to market 6 km away and back
JOURNEY = [(0, 0), (20, 4), (25, 4), (35, 6), (55, 6), (75, 0)]


def avg_rate(p, q):
    """Average rate of change between points p = (a, f(a)) and q = (b, f(b))."""
    (a, fa), (b, fb) = p, q
    if a == b:
        raise ValueError("the two times must differ")
    return F(fb - fa, b - a)


def describe(rate):
    """Word for the behaviour of a segment with the given rate."""
    if rate > 0:
        return "increasing (moving away)"
    if rate < 0:
        return "decreasing (coming back)"
    return "constant (stopped)"


def segment_rates(points):
    """Rates on consecutive segments, as (start, end, rate) triples."""
    return [(p[0], q[0], avg_rate(p, q)) for p, q in zip(points, points[1:])]


def weighted_average_holds(points, i, j, k):
    """Check (t_k - t_i) R(i, k) == (t_j - t_i) R(i, j) + (t_k - t_j) R(j, k)."""
    pi, pj, pk = points[i], points[j], points[k]
    whole = (pk[0] - pi[0]) * avg_rate(pi, pk)
    parts = (pj[0] - pi[0]) * avg_rate(pi, pj) + (pk[0] - pj[0]) * avg_rate(pj, pk)
    return whole == parts


def distance_ridden(points):
    """Total distance travelled: the sum of the sizes of all the changes."""
    return sum(abs(q[1] - p[1]) for p, q in zip(points, points[1:]))


def round_trip_speed(u, v):
    """Average speed for equal distances at speeds u and v: 2uv / (u + v)."""
    if u <= 0 or v <= 0:
        raise ValueError("speeds must be positive")
    return F(2 * u * v, u + v)


def main():
    print("1. Segments of the journey (rates in km/h = 60 x km per minute)")
    for start, end, rate in segment_rates(JOURNEY):
        kmh = 60 * rate
        print(f"   {start:>2}-{end:>2} min: {str(kmh):>4} km/h  {describe(rate)}")
    print()
    print("2. Combining intervals: the rate over 0-35 min is the length-weighted")
    print("   average of the rates on its pieces 0-20, 20-25 and 25-35:")
    r = 60 * avg_rate(JOURNEY[0], JOURNEY[3])
    print(f"   (20 x 12 + 5 x 0 + 10 x 12) / 35 = {r} = {float(r):.2f} km/h")
    triples = [(i, j, k) for i in range(len(JOURNEY))
               for j in range(i + 1, len(JOURNEY))
               for k in range(j + 1, len(JOURNEY))]
    ok = all(weighted_average_holds(JOURNEY, *t) for t in triples)
    print(f"   rule checked for all {len(triples)} triples of table times: {ok}")
    print()
    whole = avg_rate(JOURNEY[0], JOURNEY[-1])
    ridden = distance_ridden(JOURNEY)
    hours = F(JOURNEY[-1][0], 60)
    print("3. The whole trip, 0-75 min:")
    print(f"   average rate of change of distance from home: {whole} km/h")
    print(f"   distance actually ridden: {ridden} km in {hours} h,")
    speed = ridden / hours
    print(f"   so the average speed is {speed} = {float(speed):.1f} km/h")
    print()
    print("4. Round trips, equal distances at speeds u and v (km/h):")
    for u, v in [(30, 60), (10, 20), (12, 18), (40, 40)]:
        avg = round_trip_speed(u, v)
        print(f"   u = {u:>2}, v = {v:>2}: average {str(avg):>5}"
              f" = {float(avg):5.2f}, mean of speeds {F(u + v, 2)}")
    print()
    print("Epistemic status: exact rational arithmetic (decimals are rounded for")
    print("display) on one made-up journey and four pairs of speeds. The lesson")
    print("proves the general facts: the weighted-average rule, and that a round")
    print("trip's average speed is never more than the mean of the two speeds")
    print("(equal only when the speeds are equal).")


if __name__ == "__main__":
    main()
