"""Composing finite functions: associativity, identities and order.

A function on a finite set X is stored as a dict {x: f(x)}. The composite
g o f ("g after f") sends x to g(f(x)). On the 3-element set X = {0, 1, 2} we
check associativity h o (g o f) = (h o g) o f for every triple of functions,
check the identity laws, and search for functions with g o f != f o g.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product
import textwrap

EXPERIMENT = {
    "id": "composition_check",
    "title": "Composing functions: associative, but order matters",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["composition", "arrows-that-compose"],
    "summary": (
        "Checks associativity of composition on all 19683 triples of functions on "
        "a 3-element set and the identity laws on all 27 functions (a proof for "
        "that set only), and finds functions with g o f != f o g, a counterexample "
        "showing composition is not commutative in general."
    ),
    "packages": [],
}

X = (0, 1, 2)


def all_functions(domain, codomain=None):
    """Return every function domain -> codomain (default: domain -> domain) as a dict."""
    domain = list(domain)
    codomain = domain if codomain is None else list(codomain)
    return [dict(zip(domain, values)) for values in product(codomain, repeat=len(domain))]


def identity(domain):
    """The identity function on ``domain``: every x goes to itself."""
    return {x: x for x in domain}


def compose(g, f):
    """Return g o f, the function x -> g(f(x)) ("first f, then g").

    Raises ValueError if some output of f is not an input of g, because then
    g o f is not defined.
    """
    missing = set(f.values()) - set(g)
    if missing:
        raise ValueError(f"g o f is undefined: g has no value at {sorted(missing)}")
    return {x: g[f[x]] for x in f}


def show(f):
    """Write a function on 0..n-1 as its list of values, e.g. [1, 0, 2] means 0->1, 1->0, 2->2."""
    return "[" + ", ".join(str(f[x]) for x in sorted(f)) + "]"


def check_associativity(functions):
    """Check h o (g o f) == (h o g) o f for all triples; return (triples, failures)."""
    triples = 0
    failures = []
    for f, g, h in product(functions, repeat=3):
        triples += 1
        if compose(h, compose(g, f)) != compose(compose(h, g), f):
            failures.append((f, g, h))
    return triples, failures


def check_identity_laws(functions, domain):
    """Check id o f == f == f o id for every f; return (functions_checked, failures)."""
    ident = identity(domain)
    failures = [f for f in functions if not (compose(ident, f) == f == compose(f, ident))]
    return len(functions), failures


def commuting_pairs(functions):
    """Return the list of ordered pairs (f, g) with g o f == f o g."""
    return [(f, g) for f, g in product(functions, repeat=2) if compose(g, f) == compose(f, g)]


def first_noncommuting_pair(functions):
    """Return the first ordered pair (f, g) with g o f != f o g, or None if all commute."""
    for f, g in product(functions, repeat=2):
        if compose(g, f) != compose(f, g):
            return f, g
    return None


def main():
    functions = all_functions(X)
    n = len(functions)
    print(f"X = {{0, 1, 2}} has 3^3 = {n} functions X -> X.")
    print("A function is written as its list of values: [1, 0, 2] means 0->1, 1->0, 2->2.")
    print("g o f means 'first f, then g': (g o f)(x) = g(f(x)).")
    print()
    triples, failures = check_associativity(functions)
    print(f"Associativity h o (g o f) = (h o g) o f: {triples} triples checked, {len(failures)} failures")
    checked, failures = check_identity_laws(functions, X)
    print(f"Identity laws id o f = f = f o id:     {checked} functions checked, {len(failures)} failures")
    print()
    f, g = first_noncommuting_pair(functions)
    print("But order matters. First pair found with g o f != f o g:")
    print(f"  f = {show(f)}   g = {show(g)}")
    print(f"  g o f = {show(compose(g, f))}   f o g = {show(compose(f, g))}")
    swap, cycle = {0: 1, 1: 0, 2: 2}, {0: 1, 1: 2, 2: 0}
    print("A friendlier pair: s = swap 0 and 1, r = rotate 0->1->2->0:")
    print(f"  s = {show(swap)}   r = {show(cycle)}")
    print(f"  r o s = {show(compose(cycle, swap))}   s o r = {show(compose(swap, cycle))}")
    pairs = commuting_pairs(functions)
    print(f"Only {len(pairs)} of the {n * n} ordered pairs commute.")
    print()
    print("Why associativity always holds: both sides send x to h(g(f(x))).")
    print()
    print(textwrap.fill(
        f"Epistemic status: all {triples} triples and all {n} functions on this "
        "3-element set were checked, a proof by exhaustion for this set only; the "
        "one-line argument above proves associativity for all functions. A single "
        "non-commuting pair is a genuine counterexample: composition is not "
        "commutative in general.",
        width=78,
    ))


if __name__ == "__main__":
    main()
