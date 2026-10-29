"""Khovanov homology of small knots: a categorification you can compute.

Khovanov replaced the Kauffman state sum for the Jones polynomial by a chain
complex: each of the 2^n smoothings of an n-crossing diagram with k circles
contributes V^(x)k, where V = Q[x]/(x^2) has basis v+ (q-degree +1) and v-
(q-degree -1), and the edges of the cube of smoothings carry the
multiplication and comultiplication of V. The graded Euler characteristic of
the complex is the unnormalised Jones polynomial J^(q); its homology Kh is a
finer invariant. We build the complex exactly (rational arithmetic) from a PD
code, check d o d = 0, compute J^ and Kh over Q for the trefoil and the
figure-eight knot, and see that Kh has more terms than J^: for the
figure-eight knot J^ = q^-5 + q^5 but Kh has total rank 6. Exact computation
for these diagrams only; that Kh is a knot invariant is Khovanov's theorem.
"""

from fractions import Fraction
from itertools import product

EXPERIMENT = {
    "id": "categorical_representation_theory_khovanov",
    "title": "Khovanov homology of the trefoil and figure-eight knots",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["categorical-representation-theory"],
    "summary": (
        "Builds Khovanov's cube of smoothings from a PD code, with the Frobenius "
        "algebra Q[x]/(x^2) on circles, checks d o d = 0, and computes the graded "
        "Euler characteristic (the unnormalised Jones polynomial) and the rational "
        "Khovanov homology of the left-handed trefoil and the figure-eight knot. "
        "Exact for these diagrams; invariance is Khovanov's theorem."
    ),
    "packages": [],
}

# PD codes (Knot Atlas conventions): X[i, j, k, l] lists the edges at a
# crossing counterclockwise, starting from the incoming under-strand.
KNOTS = {
    "trefoil 3_1": [(1, 4, 2, 5), (3, 6, 4, 1), (5, 2, 6, 3)],
    "figure-eight 4_1": [(4, 2, 5, 1), (8, 6, 1, 5), (6, 3, 7, 4),
                         (2, 7, 3, 8)],
}


def crossing_sign(x):
    """+1 for a positive crossing: the over-strand runs from l to j."""
    _, j, _, l = x
    return 1 if j - l == 1 or l - j > 1 else -1


def circles(pd, state):
    """Circles of a smoothing, as sorted tuple of frozensets of edge labels.

    0-smoothing joins (i, j) and (k, l); 1-smoothing joins (j, k) and (l, i).
    """
    parent = {}

    def find(a):
        parent.setdefault(a, a)
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for (i, j, k, l), s in zip(pd, state):
        pairs = [(i, j), (k, l)] if s == 0 else [(j, k), (l, i)]
        for a, b in pairs:
            parent[find(a)] = find(b)
    groups = {}
    for a in list(parent):
        groups.setdefault(find(a), set()).add(a)
    return tuple(sorted((frozenset(g) for g in groups.values()), key=min))


def generators(pd):
    """All (state, circles, labels) with labels in {+1, -1} per circle."""
    out = []
    for state in product((0, 1), repeat=len(pd)):
        circ = circles(pd, state)
        for labels in product((1, -1), repeat=len(circ)):
            out.append((state, circ, labels))
    return out


def degrees(pd, gen):
    """(homological degree t, quantum degree q) of a generator."""
    n_minus = sum(1 for x in pd if crossing_sign(x) < 0)
    n_plus = len(pd) - n_minus
    state, _, labels = gen
    r = sum(state)
    return r - n_minus, sum(labels) + r + n_plus - 2 * n_minus


def differential(pd, gen):
    """d(gen) as a dict {(state, labels): coefficient}."""
    state, circ, labels = gen
    lab = dict(zip(circ, labels))
    out = {}
    for c, s in enumerate(state):
        if s == 1:
            continue
        sign = (-1) ** sum(state[:c])
        new_state = state[:c] + (1,) + state[c + 1:]
        new_circ = circles(pd, new_state)
        i, j, k, l = pd[c]
        touched = [z for z in circ if z & {i, j, k, l}]
        fixed = {z: lab[z] for z in circ if z not in touched}
        new_touched = [z for z in new_circ if z not in fixed]
        results = []  # list of (labels for new_touched circles, coefficient)
        if len(touched) == 2:  # merge two circles into one
            a, b = lab[touched[0]], lab[touched[1]]
            if a == 1 and b == 1:
                results = [((1,), 1)]
            elif a + b == 0:
                results = [((-1,), 1)]
        else:  # split one circle into two
            if lab[touched[0]] == 1:
                results = [((1, -1), 1), ((-1, 1), 1)]
            else:
                results = [((-1, -1), 1)]
        for vals, coef in results:
            full = dict(fixed)
            full.update(zip(new_touched, vals))
            key = (new_state, tuple(full[z] for z in new_circ))
            out[key] = out.get(key, 0) + sign * coef
    return {k: v for k, v in out.items() if v}


def rank(rows):
    """Rank of a rational matrix (list of rows) by Gaussian elimination."""
    m = [[Fraction(v) for v in r] for r in rows]
    rk, cols = 0, len(m[0]) if m else 0
    for c in range(cols):
        piv = next((i for i in range(rk, len(m)) if m[i][c]), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][c]:
                t = m[i][c] / m[rk][c]
                m[i] = [a - t * b for a, b in zip(m[i], m[rk])]
        rk += 1
    return rk


def khovanov(pd):
    """Return (chain dims, homology dims), both dicts {(t, q): dimension}."""
    gens = generators(pd)
    key = {(g[0], g[2]): g for g in gens}
    by_deg = {}
    for g in gens:
        by_deg.setdefault(degrees(pd, g), []).append(g)
    chain = {d: len(v) for d, v in by_deg.items()}

    def d_rank(t, q):
        src, dst = by_deg.get((t, q), []), by_deg.get((t + 1, q), [])
        if not src or not dst:
            return 0
        index = {(g[0], g[2]): n for n, g in enumerate(dst)}
        rows = [[0] * len(src) for _ in dst]
        for col, g in enumerate(src):
            for target, coef in differential(pd, g).items():
                assert target in key and degrees(pd, key[target]) == (t + 1, q)
                rows[index[target]][col] += coef
        return rank(rows)

    homology = {}
    for (t, q), dim in chain.items():
        h = dim - d_rank(t, q) - d_rank(t - 1, q)
        if h:
            homology[(t, q)] = h
    return chain, homology


def d_squared_is_zero(pd):
    """Check d(d(g)) = 0 for every generator."""
    gens = generators(pd)
    key = {(g[0], g[2]): g for g in gens}
    for g in gens:
        total = {}
        for target, c in differential(pd, g).items():
            for t2, c2 in differential(pd, key[target]).items():
                total[t2] = total.get(t2, 0) + c * c2
        if any(total.values()):
            return False
    return True


def euler(dims):
    """Graded Euler characteristic: {q-power: coefficient}."""
    poly = {}
    for (t, q), d in dims.items():
        poly[q] = poly.get(q, 0) + (-1) ** t * d
    return {q: c for q, c in sorted(poly.items()) if c}


def show_poly(poly):
    """Format {power: coefficient} as a Laurent polynomial in q."""
    out = ""
    for q, c in poly.items():
        mag = "" if abs(c) == 1 else str(abs(c))
        if not out:
            out = ("-" if c < 0 else "") + f"{mag}q^{q}"
        else:
            out += (" - " if c < 0 else " + ") + f"{mag}q^{q}"
    return out


def show_kh(dims):
    """Format {(t, q): dim} as a Poincare polynomial in t and q."""
    parts = []
    for (t, q), d in sorted(dims.items()):
        mag = "" if d == 1 else str(d)
        parts.append(f"{mag}t^{t}q^{q}")
    return " + ".join(parts)


def main():
    for name, pd in KNOTS.items():
        chain, kh = khovanov(pd)
        writhe = sum(crossing_sign(x) for x in pd)
        print(f"{name}: {len(pd)} crossings, writhe {writhe}, "
              f"{2 ** len(pd)} smoothings, chain rank {sum(chain.values())}")
        print("  d o d = 0:", d_squared_is_zero(pd))
        print("  Euler char of chain complex J^ =", show_poly(euler(chain)))
        print("  Kh over Q =", show_kh(kh))
        print(f"  total rank of Kh = {sum(kh.values())};"
              f" Euler char of Kh = J^: {euler(kh) == euler(chain)}")
    print()
    print("Epistemic status: exact rational linear algebra on the full cube")
    print("of smoothings for these two diagrams (generators, d o d = 0, ranks).")
    print("It shows homology carrying more information than its Euler")
    print("characteristic here; it does not prove that Kh is a knot invariant")
    print("(Khovanov 2000; Bar-Natan 2002), nor say anything about other knots.")


if __name__ == "__main__":
    main()
