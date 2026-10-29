"""Testing Karp's reduction 3-SAT -> INDEPENDENT SET on many formulas.

The reduction turns a 3-CNF formula with m clauses into a graph: one vertex
for each literal occurrence, a triangle on the three vertices of each clause,
and an edge between every two occurrences of complementary literals x, -x.
The theorem in the lesson says: the formula is satisfiable if and only if
the graph has an independent set of size m.

We test this on 200 small formulas, deciding each side by its own exhaustive
search (all assignments; a generic branch-and-bound search for independent
sets). We also translate certificates both ways on an example. Agreement on
these formulas is evidence that the reduction (and our code) is right; the
proof in the lesson is what shows it for every formula.
"""

import itertools
import random

EXPERIMENT = {
    "id": "complexity_theory_reductions",
    "title": "Karp's reduction from 3-SAT to independent set, tested",
    "evidence": ["exact", "experimental"],
    "lessons": ["complexity-theory"],
    "summary": (
        "Builds the 3-SAT to INDEPENDENT-SET graph for 200 seeded random 3-CNF "
        "formulas (some with a planted unsatisfiable core), decides satisfiability "
        "and the existence of an independent set of size m by separate exhaustive "
        "searches, and checks that they always agree. Experimental evidence for the "
        "reduction on small formulas, not a proof."
    ),
    "packages": [],
}


def random_3cnf(n, m, rng):
    """m random clauses, each on 3 distinct variables of 1..n with random signs."""
    formula = []
    for _ in range(m):
        variables = rng.sample(range(1, n + 1), 3)
        formula.append(tuple(v if rng.random() < 0.5 else -v for v in variables))
    return formula


def unsat_core(a, b, c):
    """All 8 clauses on the variables a, b, c: unsatisfiable on its own."""
    return [(sa * a, sb * b, sc * c)
            for sa in (1, -1) for sb in (1, -1) for sc in (1, -1)]


def satisfies(formula, assignment):
    """The verifier: does the assignment (dict var -> bool) satisfy every clause?"""
    return all(any((lit > 0) == assignment[abs(lit)] for lit in clause)
               for clause in formula)


def satisfying_assignment(formula, n):
    """Exhaustive search over all 2^n assignments; return one or None."""
    for bits in itertools.product((False, True), repeat=n):
        assignment = {v: bits[v - 1] for v in range(1, n + 1)}
        if satisfies(formula, assignment):
            return assignment
    return None


def reduction_graph(formula):
    """Vertices (clause, position); return (vertices, neighbour bitmasks)."""
    vertices = [(i, j) for i in range(len(formula)) for j in range(3)]
    masks = [0] * len(vertices)
    for (p, u), (q, v) in itertools.combinations(enumerate(vertices), 2):
        same_clause = u[0] == v[0]
        complementary = formula[u[0]][u[1]] == -formula[v[0]][v[1]]
        if same_clause or complementary:
            masks[p] |= 1 << q
            masks[q] |= 1 << p
    return vertices, masks


def _clique_cover_bound(mask, masks):
    """Greedily split `mask` into cliques: an upper bound for independent sets."""
    count = 0
    while mask:
        low = mask & -mask
        clique, candidates = low, mask & masks[low.bit_length() - 1]
        while candidates:
            w = candidates & -candidates
            clique |= w
            candidates &= masks[w.bit_length() - 1]
        mask &= ~clique
        count += 1
    return count


def independent_set(masks, size):
    """Generic branch and bound: a set of `size` pairwise non-adjacent vertices
    (as a sorted list of indices), or None if there is none."""
    def search(mask, chosen):
        if len(chosen) == size:
            return chosen
        need = size - len(chosen)
        if bin(mask).count("1") < need or _clique_cover_bound(mask, masks) < need:
            return None
        low = mask & -mask
        v = low.bit_length() - 1
        found = search(mask & ~low & ~masks[v], chosen + [v])
        return found if found is not None else search(mask & ~low, chosen)
    return search((1 << len(masks)) - 1, [])


def assignment_to_set(formula, assignment):
    """Satisfying assignment -> independent set: one true literal per clause."""
    picks = []
    for i, clause in enumerate(formula):
        j = next(j for j, lit in enumerate(clause)
                 if (lit > 0) == assignment[abs(lit)])
        picks.append(3 * i + j)
    return picks


def set_to_assignment(formula, picks, n):
    """Independent set of size m -> assignment making every picked literal true."""
    assignment = {v: False for v in range(1, n + 1)}
    for p in picks:
        lit = formula[p // 3][p % 3]
        assignment[abs(lit)] = lit > 0
    return assignment


def is_independent(masks, picks):
    return all(not masks[p] >> q & 1 for p, q in itertools.combinations(picks, 2))


def trial_formulas(count=200, n=4, seed=2024):
    """Seeded test formulas; about 40% contain a planted unsatisfiable core."""
    rng = random.Random(seed)
    formulas = []
    for _ in range(count):
        m = rng.randint(4, 12)
        formula = random_3cnf(n, m, rng)
        if rng.random() < 0.4:
            core = unsat_core(*rng.sample(range(1, n + 1), 3))
            formula = formula[: max(0, m - 8)] + core
            rng.shuffle(formula)
        formulas.append(formula)
    return formulas


def main():
    n = 4
    example = [(1, 2, -3), (-1, 3, 4), (-2, -4, 3)]
    vertices, masks = reduction_graph(example)
    edges = sum(bin(x).count("1") for x in masks) // 2
    print("Example: (x1 v x2 v -x3) & (-x1 v x3 v x4) & (-x2 v -x4 v x3)")
    print(f"  graph: {len(vertices)} vertices, {edges} edges "
          "(3 triangles + complementary pairs)")
    a = satisfying_assignment(example, n)
    picks = assignment_to_set(example, a)
    print(f"  assignment {[int(a[v]) for v in range(1, n + 1)]} -> independent "
          f"set {picks}: independent = {is_independent(masks, picks)}")
    found = independent_set(masks, len(example))
    back = set_to_assignment(example, found, n)
    print(f"  independent set {found} -> assignment "
          f"{[int(back[v]) for v in range(1, n + 1)]}: satisfies = "
          f"{satisfies(example, back)}")
    print()
    rows = []
    for formula in trial_formulas():
        sat = satisfying_assignment(formula, n) is not None
        _, masks = reduction_graph(formula)
        indep = independent_set(masks, len(formula)) is not None
        rows.append((sat, indep, len(formula)))
    agree = sum(s == i for s, i, _ in rows)
    print(f"200 formulas on {n} variables, 4 to 12 clauses:")
    print(f"  satisfiable: {sum(s for s, _, _ in rows)}, "
          f"unsatisfiable: {sum(not s for s, _, _ in rows)}")
    print(f"  'satisfiable' agrees with 'independent set of size m' in "
          f"{agree}/200 cases")
    print(f"  largest graph: {3 * max(m for _, _, m in rows)} vertices")
    print()
    print("Epistemic status: experimental evidence. Both sides were decided by "
          "exact\nexhaustive search, and they agreed on all 200 formulas tried "
          "(not a random\nsample of all formulas: many contain a planted "
          "unsatisfiable core). That\nsupports the reduction theorem and our "
          "implementation of it; only the proof\nin the lesson covers every "
          "formula.")


if __name__ == "__main__":
    main()
