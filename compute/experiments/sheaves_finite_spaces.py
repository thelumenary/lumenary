"""Sheaves on finite topological spaces, checked exhaustively.

On a finite space every open cover is finite and every presheaf of finite sets
can be tested completely. We take the four-point "pseudocircle" (a finite model
of the circle), test the sheaf condition for every open set and every open
cover, compare the constant presheaf with the sheaf of locally constant
functions, compute stalks, and compute the Cech cohomology of the locally
constant sheaf Z/2 for a two-set cover. Exhaustive checks on one small space;
the general statements are the theorems of the lesson.
"""

from itertools import combinations, product

EXPERIMENT = {
    "id": "sheaves_finite_spaces",
    "title": "Sheaves on finite spaces: gluing, stalks and a first H^1",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["sheaves"],
    "summary": (
        "On the four-point pseudocircle it tests the sheaf condition for every open "
        "set and every open cover: the constant presheaf fails, the locally constant "
        "functions pass. It computes stalks as sections over minimal neighbourhoods "
        "and the Cech H^1 of the locally constant sheaf Z/2, which is Z/2 as for "
        "the circle and 0 for a finite model of an interval. Exhaustive for these "
        "spaces only."
    ),
    "packages": [],
}

#: The pseudocircle: a, b open points, c, d closed points.
PSEUDOCIRCLE = ["a", "b", "c", "d"]
PSEUDOCIRCLE_OPENS = [set(), {"a"}, {"b"}, {"a", "b"}, {"a", "b", "c"},
                      {"a", "b", "d"}, {"a", "b", "c", "d"}]
#: A finite model of an interval: a open, c, d closed.
INTERVAL = ["a", "c", "d"]
INTERVAL_OPENS = [set(), {"a"}, {"a", "c"}, {"a", "d"}, {"a", "c", "d"}]


def opens_of(opens):
    """The open sets as frozensets, smallest first."""
    return sorted({frozenset(u) for u in opens}, key=lambda u: (len(u), sorted(u)))


def minimal_nbhd(x, opens):
    """The smallest open set containing x (it exists in a finite space)."""
    return frozenset.intersection(*[u for u in opens if x in u])


def locally_constant(u, opens, values):
    """Sections over u: functions u -> values constant on each U_x, x in u."""
    pts = sorted(u)
    sections = []
    for vals in product(values, repeat=len(pts)):
        f = dict(zip(pts, vals))
        if all(len({f[y] for y in minimal_nbhd(x, opens)}) == 1 for x in pts):
            sections.append(tuple(sorted(f.items())))
    return sections


def restrict(section, v):
    """Restrict a function (stored as sorted pairs) to the subset v."""
    return tuple((x, y) for x, y in section if x in v)


def constant_repaired(u):
    """The constant presheaf {0, 1} with a single section over the empty set."""
    return [0, 1] if u else [None]


def restrict_repaired(s, w):
    """Restriction for constant_repaired: identity, except onto the empty set."""
    return s if w else None


def sheaf_failures(opens, sec, res):
    """All (open set, cover) pairs where unique gluing fails."""
    failures = []
    for u in opens:
        subs = [w for w in opens if w <= u]
        for k in range(len(subs) + 1):
            for cover in combinations(subs, k):
                if frozenset().union(*cover) != u:
                    continue
                images = {}
                for s in sec(u):
                    key = tuple(res(s, w) for w in cover)
                    images[key] = images.get(key, 0) + 1
                compatible = [fam for fam in product(*[sec(w) for w in cover])
                              if all(res(fam[i], cover[i] & cover[j]) ==
                                     res(fam[j], cover[i] & cover[j])
                                     for i in range(k) for j in range(k))]
                if any(images.get(f, 0) != 1 for f in compatible) or \
                        len(images) != len(compatible):
                    failures.append((u, cover))
    return failures


def cech_h1_dimension(cover, opens):
    """dim over Z/2 of H^0 and H^1 for the locally constant sheaf Z/2 and a
    cover by two open sets U, V: C^0 = F(U) x F(V) -> C^1 = F(U & V)."""
    u, v = cover
    su = locally_constant(u, opens, (0, 1))
    sv = locally_constant(v, opens, (0, 1))
    suv = locally_constant(u & v, opens, (0, 1))
    image = set()
    kernel = 0
    for s, t in product(su, sv):
        diff = tuple((x, (a + b) % 2) for (x, a), (_, b) in
                     zip(restrict(s, u & v), restrict(t, u & v)))
        image.add(diff)
        kernel += all(a == 0 for _, a in diff)
    h0 = kernel.bit_length() - 1
    h1 = (len(suv) // len(image)).bit_length() - 1
    return h0, h1


def main():
    opens = opens_of(PSEUDOCIRCLE_OPENS)
    print("Pseudocircle X = {a, b, c, d}: a, b open points; 7 open sets")
    const = sheaf_failures(opens, lambda u: [0, 1], lambda s, w: s)
    print(f"constant presheaf U -> {{0,1}}: fails on {len(const)} (U, cover):")
    print("  U = empty set, empty cover (two sections over the empty set)")
    repaired = sheaf_failures(opens, constant_repaired, restrict_repaired)
    print(f"same, one section over the empty set: fails on {len(repaired)} pairs")
    disc = [(sorted(u), [sorted(w) for w in c]) for u, c in repaired
            if len(c) == 2][0]
    print(f"  e.g. U = {disc[0]} covered by {disc[1]}: 0 on one piece and 1")
    print("  on the other agree on the (empty) overlap but do not glue")

    def lc(u):
        return locally_constant(u, opens, (0, 1))
    good = sheaf_failures(opens, lc, restrict)
    print(f"locally constant functions to {{0,1}}: {len(good)} failures")
    print()
    print("number of sections of the locally constant sheaf F:")
    names = ["".join(sorted(u)) or "{}" for u in opens]
    print("  U:    " + "".join(f"{n:>6}" for n in names))
    print("  |F(U)|" + "".join(f"{len(lc(u)):>6}" for u in opens))
    stalks = {x: len(lc(minimal_nbhd(x, opens))) for x in PSEUDOCIRCLE}
    print(f"stalks F_x = F(U_x), sizes: {stalks}")
    print()
    uc, ud = frozenset("abc"), frozenset("abd")
    h0, h1 = cech_h1_dimension((uc, ud), opens)
    print(f"Cech, cover {{abc, abd}} of the pseudocircle: dim H^0 = {h0}, "
          f"dim H^1 = {h1}")
    iopens = opens_of(INTERVAL_OPENS)
    h0i, h1i = cech_h1_dimension((frozenset("ac"), frozenset("ad")), iopens)
    print(f"Cech, cover {{ac, ad}} of the finite interval: dim H^0 = {h0i}, "
          f"dim H^1 = {h1i}")
    print()
    print("Epistemic status: exhaustive over every open set and every open")
    print("cover of these two finite spaces, so for them the statements are")
    print("proved by enumeration. That the pseudocircle is a finite model of")
    print("the circle (McCord, 1966) is a theorem; the computation only agrees")
    print("with H^1(S^1; Z/2) = Z/2.")


if __name__ == "__main__":
    main()
