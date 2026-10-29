"""Tarski's definition of truth, run on every structure with three elements.

Formulas in the signature {R} (one binary relation) are stored as nested
tuples, and `satisfies` follows the definition of satisfaction clause by
clause: a quantifier becomes a loop over the domain, never over subsets. We
evaluate the axioms of equivalence relations, partial orders and linear
orders on all 2^(n*n) relations on {0, ..., n-1} for n <= 3, count the
models and the models up to isomorphism, and check on every structure that
isomorphic structures satisfy the same sentences. Four sentences then tell
the five partial orders on three points apart. Exact and exhaustive for
these finite domains.
"""

from itertools import permutations, product

EXPERIMENT = {
    "id": "first_order_logic_finite_models",
    "title": "Truth in every structure with at most three elements",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["first-order-logic"],
    "summary": (
        "Implements Tarski's satisfaction relation for formulas with one "
        "binary relation symbol, evaluates the axioms of equivalence "
        "relations, partial orders and linear orders on every relation on a "
        "set of at most three elements, counts models up to isomorphism, "
        "checks isomorphism invariance exhaustively, and separates the five "
        "partial orders on three points by four sentences."
    ),
    "packages": [],
}


def satisfies(domain, rel, formula, env=None):
    """Tarski's definition: is `formula` true in (domain, rel) under env?"""
    env = env or {}
    tag = formula[0]
    if tag == "R":
        return (env[formula[1]], env[formula[2]]) in rel
    if tag == "eq":
        return env[formula[1]] == env[formula[2]]
    if tag == "not":
        return not satisfies(domain, rel, formula[1], env)
    if tag == "and":
        return (satisfies(domain, rel, formula[1], env)
                and satisfies(domain, rel, formula[2], env))
    if tag == "or":
        return (satisfies(domain, rel, formula[1], env)
                or satisfies(domain, rel, formula[2], env))
    if tag == "imp":
        return (not satisfies(domain, rel, formula[1], env)
                or satisfies(domain, rel, formula[2], env))
    if tag in ("all", "some"):
        var, body = formula[1], formula[2]
        values = (satisfies(domain, rel, body, {**env, var: a})
                  for a in domain)
        return all(values) if tag == "all" else any(values)
    raise ValueError(f"unknown formula {formula!r}")


def R(x, y):
    """The atomic formula R(x, y)."""
    return ("R", x, y)


REFLEXIVE = ("all", "x", R("x", "x"))
SYMMETRIC = ("all", "x", ("all", "y", ("imp", R("x", "y"), R("y", "x"))))
TRANSITIVE = ("all", "x", ("all", "y", ("all", "z", (
    "imp", ("and", R("x", "y"), R("y", "z")), R("x", "z")))))
ANTISYMMETRIC = ("all", "x", ("all", "y", (
    "imp", ("and", R("x", "y"), R("y", "x")), ("eq", "x", "y"))))
TOTAL = ("all", "x", ("all", "y", ("or", R("x", "y"), R("y", "x"))))

THEORIES = {
    "equivalence relation": [REFLEXIVE, SYMMETRIC, TRANSITIVE],
    "partial order": [REFLEXIVE, ANTISYMMETRIC, TRANSITIVE],
    "linear order": [REFLEXIVE, ANTISYMMETRIC, TRANSITIVE, TOTAL],
}

SENTENCES = {
    "least": ("some", "x", ("all", "y", R("x", "y"))),
    "greatest": ("some", "x", ("all", "y", R("y", "x"))),
    "total": TOTAL,
    "comparable": ("some", "x", ("some", "y", (
        "and", ("not", ("eq", "x", "y")), R("x", "y")))),
}


def all_relations(n):
    """Every binary relation on {0, ..., n-1}, as a frozenset of pairs."""
    pairs = list(product(range(n), repeat=2))
    return [frozenset(p for p, keep in zip(pairs, bits) if keep)
            for bits in product((False, True), repeat=len(pairs))]


def models(n, theory):
    """Relations on {0..n-1} satisfying every sentence of the theory."""
    domain = range(n)
    return [r for r in all_relations(n)
            if all(satisfies(domain, r, s) for s in theory)]


def relabel(rel, perm):
    """The isomorphic copy of rel obtained by renaming x as perm[x]."""
    return frozenset((perm[a], perm[b]) for a, b in rel)


def canonical(rel, n):
    """A label for the isomorphism class of (range(n), rel)."""
    return min(tuple(sorted(relabel(rel, p))) for p in permutations(range(n)))


def invariance_holds(n, sentences):
    """Do all relabellings of every relation satisfy the same sentences?"""
    domain = range(n)
    for rel in all_relations(n):
        truth = [satisfies(domain, rel, s) for s in sentences]
        for perm in permutations(range(n)):
            copy = relabel(rel, perm)
            if [satisfies(domain, copy, s) for s in sentences] != truth:
                return False
    return True


def main():
    print("Models of three theories in the signature {R}, domain {0..n-1}")
    print(f"{'theory':<22}{'n=1':>5}{'n=2':>5}{'n=3':>5}   up to iso (n=3)")
    for name, theory in THEORIES.items():
        counts = [len(models(n, theory)) for n in (1, 2, 3)]
        classes = len({canonical(r, 3) for r in models(3, theory)})
        print(f"{name:<22}" + "".join(f"{c:>5}" for c in counts)
              + f"   {classes}")
    ok = invariance_holds(3, list(SENTENCES.values()))
    print("Isomorphic copies agree on all four sentences below (512")
    print(f"relations x 6 relabellings): {ok}")
    print()
    print("The partial orders on 3 points up to isomorphism, and which")
    print("sentences they satisfy (least, greatest, total, comparable):")
    seen = {}
    for r in models(3, THEORIES["partial order"]):
        seen.setdefault(canonical(r, 3), r)
    for key in sorted(seen, key=len):
        strict = sorted((a, b) for a, b in seen[key] if a != b)
        truth = ["T" if satisfies(range(3), seen[key], s) else "F"
                 for s in SENTENCES.values()]
        print(f"  x < y for (x, y) in {str(strict):<26} {' '.join(truth)}")
    print()
    print("Epistemic status: exact and exhaustive for domains with at most")
    print("three elements. Truth in an infinite structure cannot be decided")
    print("by looping over the domain, and isomorphism invariance for all")
    print("structures is the theorem proved in the lesson, not this check.")


if __name__ == "__main__":
    main()
