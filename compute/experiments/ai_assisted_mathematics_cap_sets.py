"""A toy version of the FunSearch loop for cap sets, with exact verification.

A cap set in F_3^n is a set of points with no three distinct points on a line;
over F_3, three distinct points x, y, z are collinear exactly when
x + y + z = 0. FunSearch (Romera-Paredes et al., Nature 2023) used a language
model to evolve short programs that score points; a fixed greedy algorithm
turns the scores into a cap set, and an evaluator measures its size. Here the
"programs" are just weight tables mutated at random (no language model), but
the loop has the same shape: mutate, build greedily, verify, keep the best.

Every reported cap set is checked by an independent verifier. The best sizes
found are compared with the known maxima 4, 9, 20, 45 for n = 2, ..., 5,
whose optimality was proved by mathematical arguments and computer search,
not by this experiment.
"""

import itertools
import random

EXPERIMENT = {
    "id": "ai_assisted_mathematics_cap_sets",
    "title": "Evolving greedy priorities for cap sets",
    "evidence": ["exact", "experimental"],
    "lessons": ["ai-assisted-mathematics"],
    "summary": (
        "A miniature of the FunSearch loop: random mutations of a priority "
        "table, a greedy builder and an exact verifier search for cap sets in "
        "F_3^n for n = 2, ..., 5. Each cap set found is checked exactly, so it "
        "proves a lower bound; comparison with the known maxima 4, 9, 20, 45 "
        "shows what search does and does not establish."
    ),
    "packages": [],
}

#: Largest cap sets in F_3^n for n = 1, ..., 6 (n = 4: Pellegrino 1970;
#: n = 5: Edel, Ferret, Landjev and Storme 2002; n = 6: Potechin 2008).
KNOWN_MAXIMUM = {1: 2, 2: 4, 3: 9, 4: 20, 5: 45, 6: 112}


def points(n):
    """All points of F_3^n, as tuples, in lexicographic order."""
    return list(itertools.product(range(3), repeat=n))


def third_point(x, y):
    """The z with x + y + z = 0 in F_3^n: the third point on the line xy."""
    return tuple((-a - b) % 3 for a, b in zip(x, y))


def is_cap_set(cap):
    """The verifier: no three distinct points of cap sum to zero."""
    s = set(cap)
    if len(s) != len(cap):
        return False
    return all(third_point(x, y) not in s for x, y in itertools.combinations(cap, 2))


def greedy_cap(order):
    """Add points in the given order whenever they keep the set a cap set."""
    cap, blocked = [], set()
    for p in order:
        if p in blocked:
            continue
        for q in cap:
            blocked.add(third_point(p, q))
        cap.append(p)
        blocked.add(p)
    return cap


def build(weights, pts):
    """Greedy cap set from a priority table: high weight first, ties lexicographic."""
    order = sorted(pts, key=lambda p: (-weights[p], p))
    return greedy_cap(order)


def evolve(n, rng, generations=300, children=4, mutation_rate=0.1):
    """(1 + lambda) evolution of a priority table; returns (best cap, history).

    history[g] is the best size known after generation g.
    """
    pts = points(n)
    best_w = {p: rng.random() for p in pts}
    best = build(best_w, pts)
    history = [len(best)]
    for _ in range(generations):
        if len(best) == KNOWN_MAXIMUM.get(n):
            break
        for _ in range(children):
            child = {
                p: (rng.random() if rng.random() < mutation_rate else w)
                for p, w in best_w.items()
            }
            cap = build(child, pts)
            if len(cap) >= len(best):
                best_w, best = child, cap
        history.append(len(best))
    return best, history


def main():
    rng = random.Random(2023)
    print("Mutate -> build greedily -> verify -> keep the best (seeded)")
    print("  n   points   first greedy   best found   generations   known max")
    found = {}
    for n, budget in ((2, 400), (3, 400), (4, 400), (5, 150)):
        cap, history = evolve(n, rng, generations=budget)
        assert is_cap_set(cap)
        found[n] = cap
        print(f"  {n}   {3 ** n:6d}   {history[0]:12d}   {len(cap):10d}   "
              f"{len(history) - 1:11d}   {KNOWN_MAXIMUM[n]:9d}")
    print()
    cap = sorted(found[3])
    print("A verified cap set in F_3^3 (each point written as a digit string):")
    words = ["".join(map(str, p)) for p in cap]
    print("  " + " ".join(words))
    print(f"  pairs checked: {len(cap) * (len(cap) - 1) // 2}; "
          f"third points inside: 0")
    print()
    print("Epistemic status: every cap set found is verified exactly, so each")
    print("size is a proved lower bound for the maximum cap in F_3^n. Reaching")
    print("the known maximum does not prove it is the maximum; that needs a")
    print("separate argument (for n = 4, Pellegrino's 1970 proof). Falling")
    print("short for n = 5 says nothing about the maximum: the search is a")
    print("heuristic, and its results vary with the seed and the budget.")


if __name__ == "__main__":
    main()
