"""Random 3-SAT: the satisfiability threshold and where the hard instances are.

We generate random 3-CNF formulas on n = 20 variables with m = r * n clauses
for several clause densities r, and solve each with a small DPLL solver (unit
propagation plus branching). Two things are measured:

* the fraction of satisfiable formulas, which drops from near 1 to near 0
  around r = 4.3 (a sharp threshold is conjectured for 3-SAT, near 4.27;
  for large k a sharp threshold was proved by Ding, Sly and Sun in 2015);
* the average number of branching nodes, which peaks near the threshold:
  formulas far below it are easy to satisfy, far above it easy to refute.

Every "satisfiable" answer comes with an assignment that we re-check with
the verifier; an "unsatisfiable" answer is trusted only because the search
was exhaustive. That asymmetry is the difference between NP and coNP.
"""

import random

EXPERIMENT = {
    "id": "complexity_theory_sat_threshold",
    "title": "Random 3-SAT: the satisfiability threshold and the hard region",
    "evidence": ["experimental", "statistical"],
    "lessons": ["complexity-theory"],
    "summary": (
        "Solves 30 seeded random 3-CNF formulas on 20 variables at each of eight "
        "clause densities with a DPLL solver, reporting the fraction satisfiable "
        "and the mean search effort. Every satisfiable verdict is re-checked with "
        "its certificate. Statistical evidence at one small size only; it does not "
        "establish the threshold or any complexity bound."
    ),
    "packages": [],
}


def random_3cnf(n, m, rng):
    """m clauses, each on 3 distinct variables of 1..n with random signs."""
    formula = []
    for _ in range(m):
        variables = rng.sample(range(1, n + 1), 3)
        formula.append(tuple(v if rng.random() < 0.5 else -v for v in variables))
    return formula


def verify(formula, true_literals):
    """The polynomial-time verifier: every clause contains a true literal."""
    return all(any(lit in true_literals for lit in clause) for clause in formula)


def dpll(formula, stats):
    """Return a set of true literals satisfying the formula, or None.

    stats["nodes"] counts the calls (branching nodes of the search tree).
    Variables not mentioned in the returned set may take either value."""
    stats["nodes"] += 1
    assigned = set()
    clauses = [list(c) for c in formula]
    while True:  # unit propagation
        remaining, unit = [], None
        for clause in clauses:
            if any(lit in assigned for lit in clause):
                continue
            rest = [lit for lit in clause if -lit not in assigned]
            if not rest:
                return None
            if len(rest) == 1 and unit is None:
                unit = rest[0]
            remaining.append(rest)
        clauses = remaining
        if unit is None:
            break
        assigned.add(unit)
    if not clauses:
        return assigned
    literal = min(clauses, key=len)[0]
    for choice in (literal, -literal):
        result = dpll(clauses + [[choice]], stats)
        if result is not None:
            return assigned | result
    return None


def complete(true_literals, n):
    """Extend a partial assignment: unmentioned variables become false."""
    full = set(true_literals)
    for v in range(1, n + 1):
        if v not in full and -v not in full:
            full.add(-v)
    return full


def sweep(n=20, ratios=(2, 3, 4, 4.25, 4.5, 5, 6, 8), trials=30, seed=2024):
    """For each ratio return (ratio, m, fraction satisfiable, mean nodes,
    number of certificates that failed verification)."""
    rng = random.Random(seed)
    rows = []
    for r in ratios:
        m = round(r * n)
        sat = nodes = bad = 0
        for _ in range(trials):
            formula = random_3cnf(n, m, rng)
            stats = {"nodes": 0}
            result = dpll(formula, stats)
            nodes += stats["nodes"]
            if result is not None:
                sat += 1
                if not verify(formula, complete(result, n)):
                    bad += 1
        rows.append((r, m, sat / trials, nodes / trials, bad))
    return rows


def main():
    n, trials = 20, 30
    print(f"Random 3-SAT, n = {n} variables, {trials} formulas per density r = m/n")
    print("    r     m   satisfiable   mean DPLL nodes   bad certificates")
    rows = sweep(n=n, trials=trials)
    for r, m, frac, nodes, bad in rows:
        print(f"{r:>5} {m:>5} {frac:>13.2f} {nodes:>17.1f} {bad:>18}")
    hardest = max(rows, key=lambda row: row[3])
    print(f"Hardest density in this run: r = {hardest[0]}. Brute force would "
          f"try 2^{n} = {2 ** n:,}\nassignments for every formula.")
    print()
    print("Epistemic status: statistical evidence from 240 seeded random "
          "formulas at\none small size (n = 20). It illustrates the threshold "
          "and the easy-hard-easy\npattern; it does not locate the threshold "
          "precisely (finite-size effects\nshift it), and it says nothing about "
          "worst-case complexity: P versus NP\nis about all instances, not "
          "typical ones.")


if __name__ == "__main__":
    main()
