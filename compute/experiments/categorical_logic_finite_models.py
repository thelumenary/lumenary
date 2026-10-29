"""Interpreting λ-terms in finite sets: sound, but too coarse to be complete.

The interpretation of the simply typed λ-calculus in Set sends the base type
to a set X. Two experiments with exact, exhaustive computation:

1. Church numerals n = λf.λx. f(f(...f(x))) are distinct normal forms, so no
   two are βη-equal. Over a finite X of size m their meanings f -> f^n must
   eventually repeat; we find the first coincidence for m = 1, 2, 3, 4.
2. The closed terms of type A×A -> A×A have four normal forms. Over X = {0, 1}
   there are 256 functions X×X -> X×X, and exactly the four definable ones are
   natural (commute with every map X -> X), as Yoneda predicts.

Friedman's theorem (1975) says that with an infinite base set, equality of
meanings is exactly βη-equality; part 1 shows why finiteness breaks this.
"""

import itertools
import math

EXPERIMENT = {
    "id": "categorical_logic_finite_models",
    "title": "λ-terms in finite sets: Church numerals and naturality",
    "evidence": ["exact", "exhaustive-finite", "counterexample"],
    "lessons": ["categorical-logic"],
    "summary": (
        "Computes the meaning of Church numerals over finite base sets and finds "
        "the first two distinct numerals with the same meaning (so finite models "
        "are not complete for beta-eta equality), then checks by exhaustive search "
        "that exactly four of the 256 functions X*X -> X*X on a two-element set are "
        "natural, matching the four closed normal terms of that type."
    ),
    "packages": [],
}


def all_maps(m):
    """All functions {0..m-1} -> {0..m-1}, as tuples of images."""
    return list(itertools.product(range(m), repeat=m))


def compose_power(f, n):
    """The n-th iterate f^n of a map given as a tuple."""
    result = tuple(range(len(f)))
    for _ in range(n):
        result = tuple(f[x] for x in result)
    return result


def numeral_meaning(n, m):
    """Meaning of the Church numeral n over an m-element set: f -> f^n."""
    return tuple(compose_power(f, n) for f in all_maps(m))


def first_coincidence(m, limit=40):
    """Smallest (a, b), a < b <= limit, with numerals a, b equal over m points."""
    seen = {}
    for n in range(limit + 1):
        meaning = numeral_meaning(n, m)
        if meaning in seen:
            return seen[meaning], n
        seen[meaning] = n
    return None


def definable_pair_maps():
    """Meanings of the 4 closed normal terms λp.(πᵢ p, πⱼ p) of type A×A->A×A."""
    def term(i, j):
        return lambda a, b: ((a, b)[i], (a, b)[j])
    return {f"(p{i + 1}, p{j + 1})": term(i, j) for i in (0, 1) for j in (0, 1)}


def natural_pair_maps(m):
    """All g : X×X -> X×X, X of size m, with g(h a, h b) = (h×h)(g(a, b))."""
    pts = [(a, b) for a in range(m) for b in range(m)]
    maps = all_maps(m)
    found = []
    for images in itertools.product(pts, repeat=len(pts)):
        g = dict(zip(pts, images))
        if all(g[(h[a], h[b])] == (h[g[(a, b)][0]], h[g[(a, b)][1]])
               for h in maps for (a, b) in pts):
            found.append(g)
    return found


def main():
    print("1. Church numerals over an m-element base set X")
    print("   (numeral n means f -> f^n; gap = difference of the two numerals)")
    for m in range(1, 5):
        a, b = first_coincidence(m)
        lcm = math.lcm(*range(1, m + 1))
        print(f"   m = {m}: {len(all_maps(m)):3d} maps; numerals {a:2d} and"
              f" {b:2d} first agree; gap {b - a:2d}; lcm(1..{m}) = {lcm:2d}")
    print("   Distinct normal forms, same meaning: finite models are not complete.")
    print()
    print("2. Closed terms of type A*A -> A*A, interpreted over X = {0, 1}")
    natural = natural_pair_maps(2)
    pts = [(a, b) for a in range(2) for b in range(2)]
    definable = definable_pair_maps()
    print(f"   functions X*X -> X*X: {4 ** 4}; natural ones: {len(natural)}")
    tables = [tuple(g[p] for p in pts) for g in natural]
    for name, t in definable.items():
        table = tuple(t(*p) for p in pts)
        print(f"   term {name}: natural = {table in tables}")
    print()
    print("Epistemic status: exact and exhaustive for the sets checked. Part 1")
    print("exhibits genuine pairs of non-convertible terms that a finite model")
    print("cannot tell apart; it does not test Friedman's theorem, which needs an")
    print("infinite base set. Part 2 checks naturality only for endomaps of a")
    print("two-element set; the general statement is the Yoneda lemma.")


if __name__ == "__main__":
    main()
