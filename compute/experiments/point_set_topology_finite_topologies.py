"""Every topology on a set with at most four points, found by exhaustive search.

A topology on a finite set X is a family of subsets containing the empty set
and X and closed under unions and intersections (for finite families,
closure under pairs suffices). Subsets of X are encoded as bit masks, so a
family of subsets is a set of integers. The search tries every family that
contains the empty set and X, keeps those satisfying the axioms, and sorts
the survivors by separation and connectedness properties. It also prints the
open, closed and clopen sets of the Sierpinski space. This is exact,
exhaustive evidence about finite spaces only; infinite spaces are not touched.
"""

from itertools import combinations

EXPERIMENT = {
    "id": "point_set_topology_finite_topologies",
    "title": "All topologies on a small finite set",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["point-set-topology"],
    "summary": (
        "Enumerates every family of subsets of an n-point set (n = 0 to 4) "
        "that satisfies the axioms of a topology, finding 1, 1, 4, 29 and 355 "
        "topologies, and counts how many are T0, T1 or Hausdorff and how many "
        "are connected. It shows open sets that are not closed and closed sets "
        "that are not open in the Sierpinski space. Exhaustive for these finite "
        "sets only."
    ),
    "packages": [],
}


def is_topology(n, family):
    """Whether ``family`` (a set of bit masks) is a topology on {0, ..., n-1}."""
    full = (1 << n) - 1
    if 0 not in family or full not in family:
        return False
    members = sorted(family)
    for i, a in enumerate(members):
        for b in members[i + 1:]:
            if (a | b) not in family or (a & b) not in family:
                return False
    return True


def topologies(n):
    """List every topology on an n-point set, each as a frozenset of masks."""
    full = (1 << n) - 1
    middle = [m for m in range(1, full)]
    found = []
    for k in range(len(middle) + 1):
        for extra in combinations(middle, k):
            family = frozenset({0, full, *extra})
            if is_topology(n, family):
                found.append(family)
    return found


def closed_sets(n, family):
    """The closed sets: complements of the open sets."""
    full = (1 << n) - 1
    return frozenset(full ^ u for u in family)


def is_t0(n, family):
    """T0: any two distinct points are told apart by some open set."""
    return all(
        any(((u >> x) & 1) != ((u >> y) & 1) for u in family)
        for x, y in combinations(range(n), 2)
    )


def is_t1(n, family):
    """T1: every one-point set is closed."""
    closed = closed_sets(n, family)
    return all((1 << x) in closed for x in range(n))


def is_hausdorff(n, family):
    """Hausdorff: distinct points have disjoint open neighbourhoods."""
    for x, y in combinations(range(n), 2):
        if not any((u >> x) & 1 and (v >> y) & 1 and not u & v
                   for u in family for v in family):
            return False
    return True


def is_connected(n, family):
    """Connected: the only clopen sets are the empty set and the whole set."""
    if n == 0:
        return True
    full = (1 << n) - 1
    clopen = family & closed_sets(n, family)
    return clopen == {0, full}


def census(n):
    """Counts (all, T0, T1, Hausdorff, connected) of topologies on n points."""
    tops = topologies(n)
    return (
        len(tops),
        sum(is_t0(n, t) for t in tops),
        sum(is_t1(n, t) for t in tops),
        sum(is_hausdorff(n, t) for t in tops),
        sum(is_connected(n, t) for t in tops),
    )


def show(mask, names="ab"):
    """Write a subset of a two-point set as {a}, {a, b}, ..."""
    items = [names[i] for i in range(len(names)) if (mask >> i) & 1]
    return "{" + ", ".join(items) + "}"


def main():
    print("Topologies on an n-point set, found by trying every family:")
    print("  n   all   T0   T1  Hausdorff  connected")
    for n in range(1, 5):
        total, t0, t1, t2, conn = census(n)
        print(f"  {n} {total:5d} {t0:4d} {t1:4d} {t2:10d} {conn:10d}")
    print()
    sierpinski = frozenset({0b00, 0b01, 0b11})
    opens = sorted(sierpinski)
    closed = sorted(closed_sets(2, sierpinski))
    print("Sierpinski space on {a, b} with open sets", ", ".join(map(show, opens)))
    print("  closed sets:", ", ".join(map(show, closed)))
    print("  {a} is open but not closed; {b} is closed but not open;")
    print("  only {} and {a, b} are both. It is T0 but not T1, and connected.")
    print()
    print("On a finite set, T1 already forces the discrete topology, so the")
    print("T1 and Hausdorff columns are all 1s: finite spaces with interesting")
    print("topologies are never Hausdorff.")
    print()
    print("Epistemic status: exact and exhaustive for sets of one to four")
    print("points (the totals 1, 4, 29, 355 agree with the known values, OEIS")
    print("A000798). It proves nothing about infinite spaces, where the lesson's")
    print("theorems live.")


if __name__ == "__main__":
    main()
