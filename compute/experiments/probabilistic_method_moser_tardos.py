"""The algorithmic local lemma: Moser and Tardos's resampling algorithm.

A k-CNF formula has clauses of k literals; under a uniformly random
assignment each clause fails with probability p = 2^-k. If every clause
shares variables with at most d others and e p (d + 1) <= 1, the Lovasz local
lemma says the formula is satisfiable - but its proof gives no algorithm,
and the probability that a random assignment works can be exponentially
small. Moser and Tardos (2010) showed that the obvious algorithm is fast:
start at random, and while some clause is violated, resample its variables.
The expected number of resamplings is at most m / d for m clauses. We build a
random 5-CNF instance with dependency degree at most 10 (so e p (d+1) < 1),
run the algorithm from 30 seeds, check the answers, and compare the number of
resamplings with the bound m / d and with naive rejection sampling. Seeded
simulation: statistical evidence about one instance, with every output
assignment verified exactly.
"""

import math
import random

EXPERIMENT = {
    "id": "probabilistic_method_moser_tardos",
    "title": "Moser-Tardos: the local lemma as an algorithm",
    "evidence": ["exact", "statistical"],
    "lessons": ["probabilistic-method"],
    "summary": (
        "Builds a random 5-CNF formula in which every clause meets at most 10 "
        "others, so the Lovasz local lemma applies, then runs Moser and "
        "Tardos's resampling algorithm from 30 seeds. Every output is checked "
        "to satisfy the formula; the numbers of resamplings are compared with "
        "the bound m/d and with naive rejection sampling. Seeded simulation."
    ),
    "packages": [],
}


def neighbours(clauses, index, occurrences):
    """Indices of the other clauses sharing a variable with clause index."""
    out = set()
    for var, _ in clauses[index]:
        out |= occurrences[var]
    out.discard(index)
    return out


def build_instance(n_vars, n_clauses, k, max_degree, rng, max_tries=20000):
    """Random k-CNF; a clause is kept only if all dependency degrees stay <= max_degree.

    A clause is a tuple of (variable, wanted_value) pairs; it is satisfied
    when at least one variable has its wanted value.
    """
    clauses, occurrences = [], [set() for _ in range(n_vars)]
    for _ in range(max_tries):
        if len(clauses) == n_clauses:
            break
        vars_ = rng.sample(range(n_vars), k)
        clause = tuple((v, rng.random() < 0.5) for v in vars_)
        clauses.append(clause)
        new = len(clauses) - 1
        for v in vars_:
            occurrences[v].add(new)
        touched = neighbours(clauses, new, occurrences) | {new}
        if any(len(neighbours(clauses, c, occurrences)) > max_degree
               for c in touched):
            for v in vars_:
                occurrences[v].discard(new)
            clauses.pop()
    return clauses


def max_dependency_degree(clauses, n_vars):
    """The largest number of other clauses any clause shares a variable with."""
    occurrences = [set() for _ in range(n_vars)]
    for i, clause in enumerate(clauses):
        for v, _ in clause:
            occurrences[v].add(i)
    return max(len(neighbours(clauses, i, occurrences))
               for i in range(len(clauses)))


def satisfied(clause, assignment):
    """True if some literal of the clause holds."""
    return any(assignment[v] == want for v, want in clause)


def moser_tardos(clauses, n_vars, rng):
    """Resample violated clauses until none is left; return (assignment, steps)."""
    assignment = [rng.random() < 0.5 for _ in range(n_vars)]
    steps = 0
    while True:
        bad = [c for c in clauses if not satisfied(c, assignment)]
        if not bad:
            return assignment, steps
        for v, _ in rng.choice(bad):
            assignment[v] = rng.random() < 0.5
        steps += 1


def naive_successes(clauses, n_vars, tries, rng):
    """How many of `tries` uniformly random assignments satisfy every clause."""
    hits = 0
    for _ in range(tries):
        bits = rng.getrandbits(n_vars)
        hits += all(any(((bits >> v) & 1) == want for v, want in clause)
                    for clause in clauses)
    return hits


def main():
    k, d, n_vars = 5, 10, 400
    rng = random.Random(2010)
    clauses = build_instance(n_vars, 150, k, d, rng)
    m = len(clauses)
    deg = max_dependency_degree(clauses, n_vars)
    p = 2.0 ** -k
    print(f"Random {k}-CNF: {n_vars} variables, {m} clauses, "
          f"max dependency degree {deg}")
    print(f"  LLL condition e p (d+1) = {math.e * p * (deg + 1):.3f} <= 1")
    runs = [moser_tardos(clauses, n_vars, random.Random(seed))
            for seed in range(30)]
    ok = all(all(satisfied(c, a) for c in clauses) for a, _ in runs)
    steps = sorted(s for _, s in runs)
    print(f"Moser-Tardos from 30 seeds: all outputs satisfy every clause: {ok}")
    print(f"  resamplings: mean {sum(steps) / len(steps):.1f}, "
          f"max {steps[-1]}; bound on the mean m/d = {m / deg:.1f}")
    tries = 2000
    hits = naive_successes(clauses, n_vars, tries, rng)
    print(f"Naive: {hits} of {tries} uniformly random assignments satisfy "
          "the formula;")
    print(f"  the LLL only guarantees probability >= (1 - 1/(d+1))^m = "
          f"{(1 - 1 / (deg + 1)) ** m:.1e}")
    print()
    print("Epistemic status: every output assignment is verified exactly;")
    print("the step counts and the naive success rate are statistical")
    print("evidence about one seeded instance. The bound m/d on the expected")
    print("number of resamplings is Moser and Tardos's theorem.")


if __name__ == "__main__":
    main()
