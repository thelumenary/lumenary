"""Counting Eilenberg-Moore algebras on small finite sets.

An algebra for a monad T on a set X is a map a : T X -> X satisfying the unit
law a(eta x) = x and the associativity law a(T a) = a(mu). For three monads on
Set we search *every* candidate map on small sets and count the algebras:

* maybe monad  (T X = X + {None}): algebras should be base points;
* power-set monad (T X = subsets of X, mu = union): algebras should be
  complete join-semilattices, a(S) = sup S;
* list monad, restricted to unital binary operations on a 3-element set: the
  algebra laws (checked on a finite slice of nested lists) should hold exactly
  for the associative ones, i.e. for the monoids.

Finally a "monad" with the wrong multiplication (intersection instead of
union) is caught breaking a unit law. All searches are exhaustive over the
stated finite ranges; they illustrate, but do not prove, the theorems.
"""

import itertools

EXPERIMENT = {
    "id": "monads_algebra_count",
    "title": "Counting algebras for the maybe, power-set and list monads",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["monads"],
    "summary": (
        "Searches every candidate structure map on sets with at most 3 "
        "elements: maybe-algebras are base points, power-set algebras are "
        "complete lattices (all chains this small), and among the 243 unital "
        "operations on 3 elements the list-algebra laws hold exactly for the "
        "associative ones. A fake monad (mu = intersection) breaks a unit law."
    ),
    "packages": [],
}


def maybe_algebras(n):
    """All maybe-algebras on {0..n-1}, by searching every map Option X -> X.

    A map is a tuple act of length n + 1; index n stands for None. Returns the
    maps satisfying the unit law and the associativity law.
    """
    def ev(act, o):
        return act[n if o is None else o]

    # oo ranges over the shapes None, Some None and Some (Some x).
    shapes = [None, ("some", None)] + [("some", x) for x in range(n)]
    found = []
    for act in itertools.product(range(n), repeat=n + 1):
        if any(act[x] != x for x in range(n)):
            continue
        ok = True
        for oo in shapes:
            inner = None if oo is None else oo[1]
            mapped = None if oo is None else ev(act, inner)
            ok = ok and ev(act, mapped) == ev(act, inner)
        if ok:
            found.append(act)
    return found


def subsets(n):
    """Subsets of {0..n-1} as bitmasks."""
    return list(range(1 << n))


def members(mask):
    """Elements of the subset encoded by a bitmask."""
    return [i for i in range(mask.bit_length()) if mask >> i & 1]


def is_powerset_algebra(act, n):
    """Check unit and associativity laws for a : P(X) -> X (dict on masks)."""
    if any(act[1 << x] != x for x in range(n)):
        return False
    subs = subsets(n)
    for family in range(1 << len(subs)):
        chosen = [subs[i] for i in members(family)]
        union = 0
        image = 0
        for s in chosen:
            union |= s
            image |= 1 << act[s]
        if act[image] != act[union]:
            return False
    return True


def powerset_algebras(n):
    """All power-set algebras on {0..n-1}, found by exhaustive search."""
    free = [s for s in subsets(n) if bin(s).count("1") != 1]
    found = []
    for values in itertools.product(range(n), repeat=len(free)):
        act = {1 << x: x for x in range(n)}
        act.update(zip(free, values))
        if is_powerset_algebra(act, n):
            found.append(act)
    return found


def order_of(act, n):
    """The relation x <= y iff a({x, y}) = y, as a set of pairs."""
    return {(x, y) for x in range(n) for y in range(n)
            if act[(1 << x) | (1 << y)] == y}


def is_least_upper_bound_map(act, rel, n):
    """True if a(S) is the least upper bound of S in rel, for every S."""
    for mask in subsets(n):
        s = members(mask)
        uppers = [y for y in range(n) if all((x, y) in rel for x in s)]
        if act[mask] not in uppers:
            return False
        if any((act[mask], v) not in rel for v in uppers):
            return False
    return True


def is_chain(rel, n):
    """True if rel is a total order on {0..n-1}."""
    total = all((x, y) in rel or (y, x) in rel for x in range(n)
                for y in range(n))
    anti = all(x == y or not ((x, y) in rel and (y, x) in rel)
               for x in range(n) for y in range(n))
    return total and anti


def unital_magmas(n):
    """All binary operations on {0..n-1} (as tuples of rows) with a unit."""
    out = []
    for table in itertools.product(range(n), repeat=n * n):
        rows = tuple(table[i * n:(i + 1) * n] for i in range(n))
        units = [e for e in range(n)
                 if all(rows[e][x] == x == rows[x][e] for x in range(n))]
        if units:
            out.append((rows, units[0]))
    return out


def fold(rows, unit, xs):
    """Evaluate a list by right-folding: x1 * (x2 * (... * (xn * e)))."""
    value = unit
    for x in reversed(xs):
        value = rows[x][value]
    return value


def list_algebra_law_holds(rows, unit, n, max_len=2):
    """Check fold(map fold xss) = fold(flatten xss) on a finite slice."""
    inner = [list(t) for k in range(max_len + 1)
             for t in itertools.product(range(n), repeat=k)]
    for k in range(max_len + 1):
        for xss in itertools.product(inner, repeat=k):
            lhs = fold(rows, unit, [fold(rows, unit, xs) for xs in xss])
            rhs = fold(rows, unit, [x for xs in xss for x in xs])
            if lhs != rhs:
                return False
    return True


def is_associative(rows, n):
    """True if the operation given by rows is associative."""
    return all(rows[rows[a][b]][c] == rows[a][rows[b][c]]
               for a in range(n) for b in range(n) for c in range(n))


def intersection_unit_counterexample(n):
    """Find a nonempty S with mu(P eta S) != S when mu is intersection."""
    for mask in subsets(n)[1:]:
        singletons = [1 << x for x in members(mask)]
        meet = (1 << n) - 1
        for s in singletons:
            meet &= s
        if meet != mask:
            return mask, meet
    return None


def main():
    print("Maybe monad: algebras on an n-element set")
    for n in range(4):
        count = len(maybe_algebras(n))
        print(f"  n = {n}: {count} algebra(s) among {n ** (n + 1)} maps"
              " Option X -> X")
    print("Power-set monad: algebras a : P(X) -> X found by full search")
    for n in range(1, 4):
        algebras = powerset_algebras(n)
        sups = sum(is_chain(order_of(a, n), n)
                   and is_least_upper_bound_map(a, order_of(a, n), n)
                   for a in algebras)
        print(f"  n = {n}: {len(algebras)} algebra(s); in {sups} of them "
              "a(S) = sup S in a chain")
    magmas = unital_magmas(3)
    algebra = [m for m in magmas if list_algebra_law_holds(*m, 3)]
    assoc = [m for m in magmas if is_associative(m[0], 3)]
    print("List monad: unital operations on {0, 1, 2}")
    print(f"  unital operations:                      {len(magmas)}")
    print(f"  folds obeying the list-algebra laws:    {len(algebra)}")
    print(f"  associative operations (monoids):       {len(assoc)}")
    print(f"  the two collections coincide:           {algebra == assoc}")
    mask, meet = intersection_unit_counterexample(3)
    print("Fake monad: P with mu = intersection instead of union")
    print(f"  S = {members(mask)}: mu(P eta S) = {members(meet)} != S, "
          "so the right unit law fails")
    print()
    print("Epistemic status: exhaustive search over the finite ranges shown "
          "(sets\nwith at most 3 elements; list-algebra laws checked on nested "
          "lists of\nlength at most 2). It agrees with the theorems in the "
          "lesson but proves\nthem only for these cases; the proofs (and the "
          "Lean file) cover all sets.")


if __name__ == "__main__":
    main()
