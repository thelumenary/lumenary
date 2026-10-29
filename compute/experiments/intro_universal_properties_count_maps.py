"""Testing the universal property of the product on small finite sets.

A candidate product is a set P with two maps p : P -> A and q : P -> B.
For every pair of functions f : X -> A and g : X -> B we count the maps
h : X -> P with p(h(x)) = f(x) and q(h(x)) = g(x) for all x, by listing all
maps X -> P. The universal property says the count is always exactly 1.
We test the set of ordered pairs, a 6-element product that is not made of
pairs, and two fakes: one where some counts are 0 (existence fails) and one
where counts are 4 (uniqueness fails). This is exhaustive-finite evidence
for the small sets X used here; the lesson's proof covers every X.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from collections import Counter
from itertools import product
import textwrap

EXPERIMENT = {
    "id": "intro_universal_properties_count_maps",
    "title": "Counting compatible maps into a candidate product",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["intro-universal-properties"],
    "summary": (
        "For A = {red, blue} and B = {1, 2, 3}, counts, for every pair of "
        "functions f : X -> A, g : X -> B, the maps h : X -> P compatible with "
        "them, for four candidates P. Pairs and a 6-element set of numbers give "
        "exactly one h every time; two fakes give 0 or 4. Exhaustive for the "
        "small sets X tested, not a proof for all X."
    ),
    "packages": [],
}

A = ("red", "blue")
B = (1, 2, 3)


def all_functions(domain, codomain):
    """Every function domain -> codomain, as a tuple of values in domain order."""
    return list(product(codomain, repeat=len(domain)))


def count_compatible(domain, P, p, q, f, g):
    """Number of h : domain -> P with p(h(x)) = f(x) and q(h(x)) = g(x).

    ``f``, ``g`` are tuples of values (one per element of ``domain``); ``p``,
    ``q`` are dicts on P. Every map h : domain -> P is listed and tested.
    """
    count = 0
    for h in product(P, repeat=len(domain)):
        if all(p[h[i]] == f[i] and q[h[i]] == g[i] for i in range(len(domain))):
            count += 1
    return count


def profile(domain, P, p, q):
    """Counter {number of compatible h: how many pairs (f, g) have it}."""
    fs = all_functions(domain, A)
    gs = all_functions(domain, B)
    return Counter(count_compatible(domain, P, p, q, f, g) for f in fs for g in gs)


def is_product_on(domain, P, p, q):
    """True if every pair (f, g) on ``domain`` has exactly one compatible h."""
    return set(profile(domain, P, p, q)) == {1}


def candidates():
    """The four candidate products (name, P, p, q) studied in the lesson."""
    pairs = list(product(A, B))
    six = list(range(1, 7))
    triples = [(a, b, c) for a, b in pairs for c in (0, 1)]
    return [
        ("ordered pairs A x B", pairs,
         {u: u[0] for u in pairs}, {u: u[1] for u in pairs}),
        ("numbers 1..6", six,
         {k: "red" if k <= 3 else "blue" for k in six},
         {k: (k - 1) % 3 + 1 for k in six}),
        ("A with q constant 1", list(A),
         {a: a for a in A}, {a: 1 for a in A}),
        ("A x B x {0, 1}", triples,
         {u: u[0] for u in triples}, {u: u[1] for u in triples}),
    ]


def main():
    X = ("x", "y")
    print(f"A = {{red, blue}}, B = {{1, 2, 3}}, X = {{x, y}}")
    n_pairs = len(all_functions(X, A)) * len(all_functions(X, B))
    print(f"pairs of functions (f, g): {n_pairs}")
    print("candidate P               |P|  compatible h per (f, g)   product?")
    for name, P, p, q in candidates():
        prof = profile(X, P, p, q)
        if len(prof) == 1:
            counts = "{} for all {}".format(*next(iter(prof.items())))
        else:
            counts = ", ".join(f"{k} for {v}" for k, v in sorted(prof.items()))
        verdict = "yes" if set(prof) == {1} else "no"
        print(f"{name:<25} {len(P):>3}  {counts:<24}  {verdict}")
    print()
    print("Listing maps: |A x B|^|X| = |A|^|X| * |B|^|X|")
    pairs = candidates()[0][1]
    for n in range(5):
        dom = tuple(range(n))
        lhs = len(all_functions(dom, pairs))
        rhs = len(all_functions(dom, A)) * len(all_functions(dom, B))
        print(f"  |X| = {n}: {lhs:>5} maps X -> A x B, {rhs:>5} pairs (f, g)")
    X3 = ("x", "y", "z")
    name, P, p, q = candidates()[1]
    print(f"With |X| = 3, '{name}' still gives one h each time: "
          f"{is_product_on(X3, P, p, q)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exhaustive-finite. Every pair (f, g) and every map "
        "h was checked, but only for X with 2 or 3 elements and these "
        "particular A and B. The universal property is about every set X; "
        "the lesson proves it for ordered pairs, and proves that any two "
        "products are matched by exactly one compatible bijection.",
        width=78,
    ))


if __name__ == "__main__":
    main()
