"""Consistent if and only if satisfiable: propositional resolution, tested.

The completeness theorem says a set of sentences is consistent (no proof of a
contradiction) exactly when it has a model. Its propositional shadow can be
checked by machine. Clauses are sets of literals (v or -v); the resolution
rule derives (C - {v}) U (D - {-v}) from C and D. The program saturates random
sets of 3-literal clauses under resolution, asks whether the empty clause
(a contradiction) appears, and compares the answer with a truth-table search
for a satisfying assignment: soundness says a refutation means no model, and
completeness says no model means a refutation. For the consistent sets it then
builds a model the way the Henkin-Lindenbaum proof does, deciding v1, v2, ...
in turn and keeping the set consistent, and checks the resulting assignment.
Evidence: exact and exhaustive for each clause set, but only for randomly
sampled sets over four variables.
"""

import random
from itertools import product

EXPERIMENT = {
    "id": "completeness_theorem_resolution",
    "title": "Consistent iff satisfiable: resolution versus truth tables",
    "evidence": ["exact", "experimental"],
    "lessons": ["completeness-theorem"],
    "summary": (
        "Saturates 150 random sets of 3-literal clauses over 4 variables under "
        "the resolution rule and compares 'no contradiction derivable' with "
        "'some truth assignment satisfies every clause' (soundness and "
        "completeness of resolution). For consistent sets it builds a model "
        "Lindenbaum-style, one variable at a time, and checks it. Exact for each "
        "set; the sample is random, so this tests rather than proves the theorem."
    ),
    "packages": [],
}


def resolvents(c, d):
    """All non-tautological resolvents of clauses c and d."""
    out = []
    for lit in c:
        if -lit in d:
            r = (c - {lit}) | (d - {-lit})
            if not any(-x in r for x in r):
                out.append(frozenset(r))
    return out


def refutable(clauses):
    """True if resolution derives the empty clause from ``clauses``.

    Saturates under resolution, discarding a new clause when a known clause
    is contained in it (it would add nothing: forward subsumption).
    """
    known = set(clauses)
    if frozenset() in known:
        return True
    frontier = list(known)
    while frontier:
        new = set()
        for c in frontier:
            for d in list(known):
                for r in resolvents(c, d):
                    if not r:
                        return True
                    if not any(k <= r for k in known) and r not in new:
                        new.add(r)
        known |= new
        frontier = list(new)
    return False


def satisfies(assignment, clauses):
    """Does the assignment (dict var -> bool) make every clause true?"""
    return all(any(assignment[abs(x)] == (x > 0) for x in c) for c in clauses)


def satisfiable(clauses, nvars):
    """Truth-table search for a satisfying assignment."""
    for values in product([False, True], repeat=nvars):
        if satisfies(dict(zip(range(1, nvars + 1), values)), clauses):
            return True
    return False


def lindenbaum_model(clauses, nvars):
    """Decide v1, v2, ... in turn, adding v or -v while consistency allows."""
    current, assignment = set(clauses), {}
    for v in range(1, nvars + 1):
        if not refutable(current | {frozenset([v])}):
            current.add(frozenset([v]))
            assignment[v] = True
        else:
            current.add(frozenset([-v]))
            assignment[v] = False
    return assignment


def random_clauses(rng, nvars, count, width=3):
    """``count`` random clauses, each on ``width`` distinct variables."""
    out = set()
    while len(out) < count:
        vs = rng.sample(range(1, nvars + 1), width)
        out.add(frozenset(v if rng.random() < 0.5 else -v for v in vs))
    return out


def main():
    rng = random.Random(1929)
    nvars, trials = 4, 150
    tally = {(True, False): 0, (False, True): 0, (True, True): 0,
             (False, False): 0}
    good_models = consistent = 0
    for _ in range(trials):
        clauses = random_clauses(rng, nvars, rng.randint(6, 20))
        sat, ref = satisfiable(clauses, nvars), refutable(clauses)
        tally[(sat, ref)] += 1
        if not ref:
            consistent += 1
            good_models += satisfies(lindenbaum_model(clauses, nvars), clauses)
    print(f"{trials} random sets of 6..20 three-literal clauses over {nvars} "
          "variables:")
    print(f"   satisfiable and not refutable:   {tally[(True, False)]:>4}")
    print(f"   unsatisfiable and refutable:     {tally[(False, True)]:>4}")
    print(f"   refutable yet satisfiable:       {tally[(True, True)]:>4}"
          "   (would break soundness)")
    print(f"   unsatisfiable, not refutable:    {tally[(False, False)]:>4}"
          "   (would break completeness)")
    print(f"Lindenbaum-style models for the {consistent} consistent sets:")
    print(f"   assignments that satisfy every clause: {good_models} of {consistent}")
    example = [frozenset(c) for c in ([1, 2], [1, -2], [-1, 2], [-1, -2])]
    print("A small refutation: {1,2}, {1,-2}, {-1,2}, {-1,-2}")
    print("   resolve on 2: {1} and {-1}; resolve on 1: {} (contradiction)")
    print(f"   refutable: {refutable(example)}; satisfiable: "
          f"{satisfiable(example, 2)}")
    print()
    print("Epistemic status: each verdict is exact (full saturation and a full")
    print("truth table), so every set tested agrees with soundness and")
    print("completeness. But the sets were sampled at random over four variables;")
    print("the theorem for all clause sets, and Goedel's theorem for first-order")
    print("logic, are proved in the lesson, not by this experiment.")


if __name__ == "__main__":
    main()
