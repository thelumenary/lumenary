"""The bisection proof of Heine-Borel, run as an algorithm.

To find a finite subcover of an open cover of [a, b], ask whether one set of
the cover contains the whole interval; if not, cut it in half and ask again
about each half. The proof of the Heine-Borel theorem shows that on a closed
bounded interval this always stops: an infinite chain of halvings would close
in on a point x, and the open set containing x would swallow every small
enough interval around x. We run the procedure with exact rational arithmetic
on two covers by the open intervals U_n = (1/n, 2): on [0, 1], with one extra
set around 0, it stops; on (0, 1] it never does, because the chain of
left-hand halves closes in on 0, which is not in the space. Evidence: exact
computation, and a counterexample to compactness of (0, 1].
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "point_set_topology_bisection_cover",
    "title": "Heine-Borel by bisection: finite subcovers on demand",
    "evidence": ["exact", "counterexample"],
    "lessons": ["point-set-topology"],
    "summary": (
        "Runs the bisection argument from the proof of Heine-Borel as an "
        "algorithm with exact fractions. For an open cover of [0, 1] it halts "
        "with a finite subcover; for the cover of (0, 1] by the intervals "
        "(1/n, 2) the left-most piece (0, 2^-d] is never covered, and the "
        "number of sets used grows with the depth d: (0, 1] is not compact. "
        "The runs illustrate the proof but are not themselves a proof."
    ),
    "packages": [],
}

TENTH = Fraction(1, 10)


def smallest_index_above(lo):
    """Smallest n >= 1 with 1/n < lo, for lo > 0."""
    if lo <= 0:
        raise ValueError("lo must be positive")
    return int(1 / lo) + 1


def cover_closed(lo, hi, left_open=False):
    """Cover of [0, 1]: U_0 = (-1/10, 1/10) and U_n = (1/n, 2), n >= 1.

    Returns the index of one set containing [lo, hi], or None.
    """
    if -TENTH < lo and hi < TENTH:
        return 0
    if lo > 0 and hi < 2:
        return smallest_index_above(lo)
    return None


def cover_half_open(lo, hi, left_open=False):
    """Cover of (0, 1] by U_n = (1/n, 2), n >= 1 (no set around 0).

    ``left_open`` marks the piece (lo, hi] with lo = 0, which no U_n contains.
    """
    if left_open or lo <= 0 or hi >= 2:
        return None
    return smallest_index_above(lo)


def bisect_cover(find, lo, hi, max_depth, left_open=False):
    """Run the bisection argument on [lo, hi] (or (lo, hi] if ``left_open``).

    Returns (sorted indices used, leftover pieces, deepest level reached).
    """
    used, leftovers, deepest = set(), [], 0
    stack = [(Fraction(lo), Fraction(hi), 0)]
    while stack:
        a, b, depth = stack.pop()
        deepest = max(deepest, depth)
        index = find(a, b, left_open and a == lo)
        if index is not None:
            used.add(index)
        elif depth == max_depth:
            leftovers.append((a, b))
        else:
            mid = (a + b) / 2
            stack.extend([(a, mid, depth + 1), (mid, b, depth + 1)])
    return sorted(used), leftovers, deepest


def main():
    used, left, deepest = bisect_cover(cover_closed, 0, 1, 60)
    print("Cover of [0, 1] by (-1/10, 1/10) and U_n = (1/n, 2), n >= 1:")
    print(f"  halted at depth {deepest} with no leftovers: {left == []}")
    print(f"  finite subcover: {len(used)} sets, indices {used}")
    print()
    print("Cover of (0, 1] by U_n = (1/n, 2) alone:")
    print("  depth  sets used  largest index  uncovered piece")
    for depth in (4, 8, 16, 32):
        used, left, _ = bisect_cover(cover_half_open, 0, 1, depth, True)
        (a, b), = left
        assert a == 0 and b == Fraction(1, 2**depth)
        print(f"  {depth:5d} {len(used):10d} {max(used):14d}  (0, 2^-{depth}]")
    print()
    print("Every halving leaves the piece next to 0 uncovered, and covering")
    print("[2^-d, 1] needs ever larger n. Indeed no finite subfamily covers")
    print("(0, 1]: if N is its largest index, the points of (0, 1/N] are missed.")
    print("The chain of left halves closes in on 0, a point missing from the")
    print("space. On [0, 1] that point is present and lies in an open set of")
    print("the cover, which is exactly why the procedure must halt.")
    print()
    print("Epistemic status: exact rational arithmetic on two specific covers.")
    print("It illustrates the proof of Heine-Borel and gives a counterexample")
    print("to compactness of (0, 1]; it does not prove that the procedure halts")
    print("for every open cover of [0, 1] - the lesson's proof does that.")


if __name__ == "__main__":
    main()
