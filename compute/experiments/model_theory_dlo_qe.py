"""Quantifier elimination for dense linear orders, tested against search.

A primitive formula Ex (conjunction of atoms a < x, x < b, x = c, with
parameters a, b, c) is replaced by a quantifier-free formula in the
parameters alone, following the lesson's proof: substitute if there is an
equation x = c; otherwise require every lower bound to be below every upper
bound. For random formulas and random rational parameters the program checks
the eliminated formula against a direct search for a witness x in Q, and then
shows the same elimination going wrong in the integers, which are not dense.
Evidence: exact rational arithmetic; random sampling, so it is a test, not a
proof.
"""

import random
from fractions import Fraction

EXPERIMENT = {
    "id": "model_theory_dlo_qe",
    "title": "Eliminating a quantifier in dense linear orders",
    "evidence": ["exact", "experimental", "counterexample"],
    "lessons": ["model-theory"],
    "summary": (
        "Implements the elimination of Ex from conjunctions of order atoms in a "
        "dense linear order without endpoints, then compares it with a direct "
        "witness search in Q on 2000 random formulas (exact fractions). The same "
        "elimination fails in Z, and the program finds such counterexamples. "
        "Random tests support, but do not prove, correctness."
    ),
    "packages": [],
}


def eliminate(atoms):
    """Quantifier-free equivalent of Ex /\\ atoms, as a list of (s, rel, t).

    Atoms are ('lt', a, 'x'), ('lt', 'x', b) or ('eq', 'x', c); parameters are
    names. The result is a conjunction of atoms between parameters.
    """
    eqs = [c for kind, s, c in atoms if kind == "eq"]
    if eqs:
        c = eqs[0]
        out = [("eq", c, d) for d in eqs[1:]]
        out += [("lt", c if s == "x" else s, c if t == "x" else t)
                for kind, s, t in atoms if kind == "lt"]
        return list(dict.fromkeys(out))
    lows = [s for kind, s, t in atoms if t == "x"]
    highs = [t for kind, s, t in atoms if s == "x"]
    return list(dict.fromkeys(("lt", a, b) for a in lows for b in highs))


def holds(formula, values):
    """Truth of a conjunction of parameter atoms under ``values``."""
    rel = {"lt": lambda u, v: u < v, "eq": lambda u, v: u == v}
    return all(rel[k](values[s], values[t]) for k, s, t in formula)


def candidates(values, integers=False):
    """Finitely many x that suffice to find a witness, if there is one."""
    pts = sorted(set(values.values()))
    if integers:
        return range(int(min(pts)) - 1, int(max(pts)) + 2)
    mids = [(p + q) / 2 for p, q in zip(pts, pts[1:])]
    return pts + mids + [pts[0] - 1, pts[-1] + 1]


def witness_exists(atoms, values, integers=False):
    """Search directly for x making every atom true."""
    def ok(x):
        env = dict(values, x=x)
        return holds(atoms, env)
    return any(ok(x) for x in candidates(values, integers))


def random_case(rng, names, integers=False):
    """A random primitive formula and random parameter values."""
    atoms = []
    for _ in range(rng.randint(1, 4)):
        p = rng.choice(names)
        kind = rng.choice(["lt", "lt", "lt", "eq"])
        atoms.append((kind, "x", p) if kind == "eq" or rng.random() < 0.5
                     else ("lt", p, "x"))
    pick = (lambda: rng.randint(0, 3)) if integers else (
        lambda: Fraction(rng.randint(0, 6), rng.randint(1, 3)))
    return list(dict.fromkeys(atoms)), {p: pick() for p in names}


def compare(trials, integers=False, seed=2024):
    """Count agreements and collect disagreements on random cases."""
    rng = random.Random(seed)
    agree, bad = 0, []
    for _ in range(trials):
        atoms, values = random_case(rng, ["a", "b", "c"], integers)
        if holds(eliminate(atoms), values) == witness_exists(
                atoms, values, integers):
            agree += 1
        else:
            bad.append((atoms, values))
    return agree, bad


def show(formula):
    """Pretty-print a conjunction of atoms."""
    sym = {"lt": "<", "eq": "="}
    return " and ".join(f"{s} {sym[k]} {t}" for k, s, t in formula) or "true"


def main():
    example = [("lt", "a", "x"), ("lt", "b", "x"), ("lt", "x", "c")]
    print(f"Ex ({show(example)})")
    print(f"   is equivalent in a DLO to: {show(eliminate(example))}")
    example2 = [("eq", "x", "c"), ("lt", "a", "x")]
    print(f"Ex ({show(example2)})  ~>  {show(eliminate(example2))}")
    print()
    agree, bad = compare(2000)
    print(f"In Q: 2000 random formulas, {agree} agreements, {len(bad)} failures")
    agree_z, bad_z = compare(2000, integers=True)
    print(f"In Z: 2000 random formulas, {agree_z} agreements, "
          f"{len(bad_z)} failures")
    atoms, values = min(bad_z, key=lambda case: len(case[0]))
    nice = ", ".join(f"{p} = {v}" for p, v in sorted(values.items()))
    print(f"   e.g. Ex ({show(atoms)}) with {nice}:")
    print(f"   the eliminated formula '{show(eliminate(atoms))}' is true,")
    print("   but no integer x works - Z is not dense.")
    print()
    print("Epistemic status: exact arithmetic on 2000 random formulas per order.")
    print("Agreement in Q is evidence that the elimination is implemented")
    print("correctly, not a proof; the proof is the lesson's key lemma (also")
    print("checked in Lean). The failures in Z are genuine counterexamples.")


if __name__ == "__main__":
    main()
