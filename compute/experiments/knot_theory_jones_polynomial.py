"""The Kauffman bracket and the Jones polynomial, computed from PD codes.

A knot diagram is given by a planar diagram (PD) code: one quadruple
(i, j, k, l) per crossing, listing the four edge labels anticlockwise and
starting from the incoming under-edge. The Kauffman bracket is the state sum
over all 2^n ways of smoothing the crossings,

    <D> = sum over states of A^(#A - #B) * d^(loops - 1),  d = -A^2 - A^(-2),

and the Jones polynomial is V(t) = (-A^3)^(-writhe) <D> with A = t^(-1/4).
We compute both exactly (Laurent polynomials as dictionaries exponent ->
coefficient), check that adding a kink changes the bracket by -A^(+-3) but
not V, check that V(1) = 1, and compare each knot with its mirror image.
Evidence: exact computation on these diagrams; the invariance theorems are
proved in the lesson.
"""

from collections import defaultdict
from itertools import product

EXPERIMENT = {
    "id": "knot_theory_jones_polynomial",
    "title": "Kauffman bracket and Jones polynomial from PD codes",
    "evidence": ["exact"],
    "lessons": ["knot-theory"],
    "summary": (
        "Computes the Kauffman bracket state sum and the writhe of planar "
        "diagram codes, and from them the Jones polynomial of the trefoil, its "
        "mirror, the figure-eight knot and the knots 5_1, 5_2 and 6_1. It checks "
        "that a kink multiplies the bracket by -A^3 but leaves V unchanged, that "
        "V(1) = 1, and that the trefoil's V differs from its mirror's. Exact, for "
        "these diagrams only."
    ),
    "packages": [],
}

KNOTS = {
    "3_1 (right trefoil)": [(1, 5, 2, 4), (3, 1, 4, 6), (5, 3, 6, 2)],
    "3_1 mirror (left)": [(4, 1, 5, 2), (6, 3, 1, 4), (2, 5, 3, 6)],
    "4_1 (figure eight)": [(4, 2, 5, 1), (8, 6, 1, 5), (6, 3, 7, 4),
                           (2, 7, 3, 8)],
    "5_1": [(1, 6, 2, 7), (3, 8, 4, 9), (5, 10, 6, 1), (7, 2, 8, 3),
            (9, 4, 10, 5)],
    "5_2": [(1, 4, 2, 5), (3, 8, 4, 9), (5, 10, 6, 1), (9, 6, 10, 7),
            (7, 2, 8, 3)],
    "6_1": [(1, 4, 2, 5), (7, 10, 8, 11), (3, 9, 4, 8), (9, 3, 10, 2),
            (5, 12, 6, 1), (11, 6, 12, 7)],
}


def loops(pd, state):
    """Number of circles after smoothing: A joins (i,j),(k,l); B (i,l),(j,k)."""
    parent = {}

    def find(x):
        while parent.setdefault(x, x) != x:
            x = parent[x]
        return x

    for (i, j, k, l), s in zip(pd, state):
        pairs = [(i, j), (k, l)] if s == "A" else [(i, l), (j, k)]
        for a, b in pairs:
            parent[find(a)] = find(b)
    return len({find(x) for crossing in pd for x in crossing})


def multiply(p, q):
    """Product of Laurent polynomials stored as {exponent: coefficient}."""
    out = defaultdict(int)
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            out[e1 + e2] += c1 * c2
    return {e: c for e, c in out.items() if c}


def bracket(pd):
    """The Kauffman bracket <D> as {exponent of A: coefficient}."""
    if not pd:
        return {0: 1}
    delta = {2: -1, -2: -1}
    total = defaultdict(int)
    for state in product("AB", repeat=len(pd)):
        term = {state.count("A") - state.count("B"): 1}
        for _ in range(loops(pd, state) - 1):
            term = multiply(term, delta)
        for e, c in term.items():
            total[e] += c
    return {e: c for e, c in sorted(total.items()) if c}


def crossing_sign(crossing, edges):
    """+1 if the over strand runs l -> j (right-handed), -1 if j -> l."""
    _, j, _, l = crossing
    if (j - l) % edges == 1:
        return 1
    if (l - j) % edges == 1:
        return -1
    raise ValueError("cannot orient the over strand (use n >= 2)")


def writhe(pd):
    """Sum of the crossing signs."""
    return sum(crossing_sign(x, 2 * len(pd)) for x in pd)


def jones(pd):
    """V(t) as {exponent of t: coefficient}, using A = t^(-1/4)."""
    w = writhe(pd)
    sign = -1 if w % 2 else 1
    f = {e - 3 * w: sign * c for e, c in bracket(pd).items()}
    assert all(e % 4 == 0 for e in f), "a knot's f has exponents in 4Z"
    return {-e // 4: c for e, c in sorted(f.items(), reverse=True)}


def mirror_jones(v):
    """V of the mirror image: t -> 1/t."""
    return {-e: c for e, c in sorted(v.items(), key=lambda kv: -kv[0])}


def add_kink(pd, positive=True):
    """Add a kink on the last edge 2n; returns a PD code with n + 1 crossings."""
    n2 = 2 * len(pd)
    new, g = [], n2 + 2
    for (i, j, k, l) in pd:
        # the occurrence of 2n where that edge *ends* gets the new label 2n + 2
        if i == n2:
            i = g
        elif j == n2 and l == 1:
            j = g
        elif l == n2 and j == 1:
            l = g
        new.append((i, j, k, l))
    kink = (n2, g, n2 + 1, n2 + 1) if positive else (n2, n2 + 1, n2 + 1, g)
    return new + [kink]


def show(poly, var="t"):
    """Format {exponent: coefficient} as text, highest power first."""
    terms = []
    for e, c in sorted(poly.items(), key=lambda kv: -kv[0]):
        mag = "" if abs(c) == 1 and e != 0 else str(abs(c))
        power = "" if e == 0 else (var if e == 1 else f"{var}^{e}")
        sign = "-" if c < 0 else "+"
        terms.append(f"{sign} {mag}{power}".strip())
    text = " ".join(terms)
    return text[2:] if text.startswith("+ ") else "-" + text[2:]


def main():
    trefoil = KNOTS["3_1 (right trefoil)"]
    print("Kauffman bracket of the right trefoil (8 states):")
    print("  <3_1> =", show(bracket(trefoil), "A"), " writhe", writhe(trefoil))
    for positive in (True, False):
        kinked = add_kink(trefoil, positive)
        print(f"  with a {'positive' if positive else 'negative'} kink:",
              show(bracket(kinked), "A"), " writhe", writhe(kinked))
    same = jones(add_kink(trefoil)) == jones(add_kink(trefoil, False)) \
        == jones(trefoil)
    print("  V unchanged by either kink:", same)
    print()
    print("Jones polynomials V(t):")
    for name, pd in KNOTS.items():
        v = jones(pd)
        amph = "yes" if v == mirror_jones(v) else "no"
        print(f"  {name:<20} {show(v)}")
        print(f"  {'':<20} V(1) = {sum(v.values())}, V(t) = V(1/t)? {amph}")
    print()
    print("As V is an invariant, V(1/t) != V(t) proves that 3_1, 5_1, 5_2 and")
    print("6_1 are not equivalent to their mirror images. For 4_1, V(t) = V(1/t)")
    print("is consistent with mirror symmetry but does not prove it.")
    print()
    print("Epistemic status: exact computation for these PD codes. That V is a")
    print("knot invariant (so equal knots have equal V) is a theorem proved in")
    print("the lesson; the program only evaluates it.")


if __name__ == "__main__":
    main()
