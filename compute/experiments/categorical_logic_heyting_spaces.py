"""Heyting algebras of open sets: where excluded middle fails, and where it cannot.

Every topology is a Heyting algebra: meet is intersection, join is union, and
U => V is the interior of (X \\ U) | V, the largest open W with W & U <= V.
We enumerate all 29 topologies on a three-point set, check the Heyting law
W <= (U => V)  iff  W & U <= V  exhaustively, find which topologies are
Boolean, and evaluate classical tautologies under every valuation.

A failure is a genuine countermodel: by the soundness theorem proved in the
lesson (and in Lean), a formula that is not top in some Heyting algebra is not
derivable in intuitionistic propositional logic. Success on these small spaces
is only finite evidence of derivability.
"""

import itertools

EXPERIMENT = {
    "id": "categorical_logic_heyting_spaces",
    "title": "Heyting algebras of open sets on small spaces",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["categorical-logic"],
    "summary": (
        "Enumerates all topologies on a set with at most three points, checks the "
        "Heyting residuation law exhaustively, counts the Boolean ones (exactly the "
        "partition topologies) and evaluates classical tautologies under every "
        "valuation. Failures are genuine countermodels to intuitionistic "
        "derivability; successes are evidence on finitely many algebras only."
    ),
    "packages": [],
}


def subsets(points):
    """All subsets of ``points`` as frozensets, smallest first."""
    pts = sorted(points)
    return [frozenset(c) for r in range(len(pts) + 1)
            for c in itertools.combinations(pts, r)]


def is_topology(opens, space):
    """Contains the empty set and the space, closed under union and meet."""
    if frozenset() not in opens or space not in opens:
        return False
    return all(a | b in opens and a & b in opens for a in opens for b in opens)


def all_topologies(n):
    """All topologies on {0, ..., n-1}, as a list of frozensets of opens."""
    space = frozenset(range(n))
    middle = [s for s in subsets(space) if s and s != space]
    found = []
    for k in range(len(middle) + 1):
        for family in itertools.combinations(middle, k):
            opens = frozenset(family) | {frozenset(), space}
            if is_topology(opens, space):
                found.append(opens)
    return found


def implies(opens, u, v):
    """Heyting implication: the union of all opens W with W & u <= v."""
    return frozenset().union(*[w for w in opens if w & u <= v])


def neg(opens, u):
    """Pseudo-complement: the largest open set disjoint from u."""
    return implies(opens, u, frozenset())


def residuation_holds(opens):
    """Check W <= (U => V) iff W & U <= V for all opens W, U, V."""
    return all((w <= implies(opens, u, v)) == (w & u <= v)
               for w in opens for u in opens for v in opens)


def is_boolean(opens, space):
    """Boolean iff U | not U is the whole space for every open U."""
    return all(u | neg(opens, u) == space for u in opens)


def evaluate(formula, opens, valuation):
    """Value of a formula: an atom name or (op, args...), op in and/or/imp/not."""
    if isinstance(formula, str):
        return valuation[formula]
    op, *args = formula
    vals = [evaluate(a, opens, valuation) for a in args]
    if op == "and":
        return vals[0] & vals[1]
    if op == "or":
        return vals[0] | vals[1]
    if op == "imp":
        return implies(opens, vals[0], vals[1])
    return neg(opens, vals[0])


def atoms(formula):
    """The set of atom names in a formula."""
    if isinstance(formula, str):
        return {formula}
    return set().union(*[atoms(a) for a in formula[1:]])


def countermodel(formula, max_points=3):
    """First (space, opens, valuation) where the formula is not top, or None."""
    names = sorted(atoms(formula))
    for n in range(1, max_points + 1):
        space = frozenset(range(n))
        for opens in all_topologies(n):
            ordered = sorted(opens, key=lambda s: (len(s), sorted(s)))
            for values in itertools.product(ordered, repeat=len(names)):
                valuation = dict(zip(names, values))
                if evaluate(formula, opens, valuation) != space:
                    return space, opens, valuation
    return None


FORMULAS = [
    ("p or not p", ("or", "p", ("not", "p"))),
    ("not not (p or not p)", ("not", ("not", ("or", "p", ("not", "p"))))),
    ("not not p -> p", ("imp", ("not", ("not", "p")), "p")),
    ("p -> not not p", ("imp", "p", ("not", ("not", "p")))),
    ("((p -> q) -> p) -> p", ("imp", ("imp", ("imp", "p", "q"), "p"), "p")),
    ("not p or not not p", ("or", ("not", "p"), ("not", ("not", "p")))),
    ("(p -> q) or (q -> p)", ("or", ("imp", "p", "q"), ("imp", "q", "p"))),
    ("not (p and q) -> not p or not q",
     ("imp", ("not", ("and", "p", "q")), ("or", ("not", "p"), ("not", "q")))),
]


def show(s):
    """Print a set of points compactly, e.g. {0,1}."""
    return "{" + ",".join(str(x) for x in sorted(s)) + "}"


def main():
    print("Topologies on n points; residuation law; how many are Boolean:")
    for n in range(1, 4):
        space = frozenset(range(n))
        tops = all_topologies(n)
        ok = all(residuation_holds(t) for t in tops)
        boolean = sum(is_boolean(t, space) for t in tops)
        print(f"  n = {n}: {len(tops):2d} topologies, Heyting law holds in all:"
              f" {ok}, Boolean: {boolean}")
    sierp = frozenset([frozenset(), frozenset([1]), frozenset([0, 1])])
    u = frozenset([1])
    print("Sierpinski space, opens {}, {1}, {0,1}; U = {1}:")
    print(f"  not U = {show(neg(sierp, u))}, U or not U = "
          f"{show(u | neg(sierp, u))}, not not U = {show(neg(sierp, neg(sierp, u)))}")
    print()
    print("Classical tautologies on all spaces with at most 3 points:")
    for name, formula in FORMULAS:
        found = countermodel(formula)
        if found is None:
            print(f"  {name:<34} top in every case checked")
        else:
            space, opens, val = found
            where = ", ".join(f"{k}={show(v)}" for k, v in sorted(val.items()))
            print(f"  {name:<34} FAILS: {len(space)} points, "
                  f"{len(opens)} opens, {where}")
    print()
    print("Epistemic status: exhaustive over all topologies on at most three")
    print("points. Each FAILS line is a genuine countermodel, so by soundness that")
    print("formula is not derivable intuitionistically. A formula that is top in")
    print("every case checked is only supported by finite evidence here; the")
    print("derivations (e.g. of not not (p or not p)) are what prove it.")


if __name__ == "__main__":
    main()
