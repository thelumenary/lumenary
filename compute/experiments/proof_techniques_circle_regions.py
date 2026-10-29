"""Circle regions: a pattern that breaks.

Put n points on a circle and draw every chord between them. How many regions
does the disc fall into? For n = 1, 2, 3, 4, 5 the answers are 1, 2, 4, 8, 16,
which suggests 2**(n - 1). For n = 6 the answer is 31.

We count regions exactly. The points are rational points of the unit circle,
((1 - t^2)/(1 + t^2), 2t/(1 + t^2)), so every chord crossing is computed with
exact fractions. The chords cut the disc into a connected plane graph, and
Euler's formula V - E + F = 2 then gives

    regions = 1 + (number of chords) + sum over crossing points P of (m_P - 1),

where m_P is the number of chords through P. (Each chord adds one region, and
each crossing on it adds one more.) If no three chords meet at a point this is
1 + C(n, 2) + C(n, 4), which is not a power of 2 for n = 6. If three chords
do meet - as the three diameters of a symmetric hexagon do - the count drops.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from fractions import Fraction
from itertools import combinations
from math import comb

EXPERIMENT = {
    "id": "proof_techniques_circle_regions",
    "title": "Regions of a circle: a pattern that breaks",
    "evidence": ["exact", "counterexample"],
    "lessons": ["proof-techniques"],
    "summary": (
        "Counts exactly, with rational arithmetic, the regions formed by all chords "
        "between n points on a circle (n = 1 to 8). The counts 1, 2, 4, 8, 16 "
        "suggest 2^(n-1), but n = 6 gives 31 (and 30 when three diagonals meet). "
        "The counts use Euler's formula, a theorem; the first five values alone "
        "proved nothing."
    ),
    "packages": [],
}


def circle_point(t):
    """The rational point of the unit circle with parameter t (a Fraction)."""
    t = Fraction(t)
    d = 1 + t * t
    return ((1 - t * t) / d, 2 * t / d)


def crossing(a, b, c, d):
    """The point where chords ab and cd cross strictly inside both, or None."""
    (x1, y1), (x2, y2), (x3, y3), (x4, y4) = a, b, c, d
    den = (x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3)
    if den == 0:
        return None
    s = ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3)) / den
    u = ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)) / den
    if 0 < s < 1 and 0 < u < 1:
        return (x1 + s * (x2 - x1), y1 + s * (y2 - y1))
    return None


def regions(points):
    """Number of regions into which all chords between ``points`` cut the disc."""
    chords = list(combinations(points, 2))
    through = {}
    for (i, ch1), (j, ch2) in combinations(enumerate(chords), 2):
        if set(ch1) & set(ch2):
            continue                        # chords sharing an endpoint
        p = crossing(*ch1, *ch2)
        if p is not None:
            through.setdefault(p, set()).update((i, j))
    return 1 + len(chords) + sum(len(s) - 1 for s in through.values())


def general_position_formula(n):
    """1 + C(n, 2) + C(n, 4): the count when no three chords are concurrent."""
    return 1 + comb(n, 2) + comb(n, 4)


#: Parameters giving points in general position for n <= 8.
PARAMS = [Fraction(k, 7) for k in (0, 2, 5, 9, 14, 22, 37, 61)]

#: Three antipodal pairs: the three diameters all pass through the centre.
HEXAGON_WITH_DIAMETERS = [(Fraction(1), Fraction(0)), (Fraction(-1), Fraction(0)),
                          (Fraction(3, 5), Fraction(4, 5)),
                          (Fraction(-3, 5), Fraction(-4, 5)),
                          (Fraction(-3, 5), Fraction(4, 5)),
                          (Fraction(3, 5), Fraction(-4, 5))]


def main():
    print(" n  regions  2^(n-1)  1+C(n,2)+C(n,4)")
    for n in range(1, 9):
        r = regions([circle_point(t) for t in PARAMS[:n]])
        guess = 2 ** (n - 1)
        mark = "" if r == guess else "   <- pattern broken"
        print(f"{n:2d}  {r:7d}  {guess:7d}  {general_position_formula(n):15d}{mark}")
    print()
    r6 = regions(HEXAGON_WITH_DIAMETERS)
    print(f"Six points forming three diameters (concurrent at the centre): {r6}")
    print("The count depends on the positions, not only on n.")
    print()
    print("Epistemic status: exact counts for these particular point sets, using")
    print("rational arithmetic and Euler's formula (a theorem). They refute the")
    print("guess 2^(n-1): one counterexample suffices. The general formula for")
    print("points in general position needs a proof; numbers cannot supply it.")


if __name__ == "__main__":
    main()
