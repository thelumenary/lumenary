"""A proof checker in twenty lines: why checking is easier than finding.

A proof assistant's kernel only *checks* proofs. To see how small a checker
can be, we implement one for a Hilbert-style system of propositional logic
with implication only: the axiom schemes K: A -> (B -> A) and
S: (A -> (B -> C)) -> ((A -> B) -> (A -> C)), and the rule modus ponens. We
check the classic five-line proof of p -> p, reject a faulty proof with a
precise message, and test soundness: every axiom instance and every proved
formula is a tautology (true under all truth assignments). Checking takes one
pass over the proof; *finding* a proof is a search that can grow
exponentially, which is why proof assistants combine a small kernel with
tactics that search.
"""

import itertools

EXPERIMENT = {
    "id": "formal_proof_lean_proof_checker",
    "title": "A tiny proof checker for propositional logic",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["formal-proof-lean"],
    "summary": (
        "Implements a checker for Hilbert-style proofs in implicational logic "
        "(axioms K and S, modus ponens), checks the five-line proof of p -> p, "
        "rejects a faulty proof with a precise error, and confirms by truth "
        "tables that every axiom instance tried and every proved formula is a "
        "tautology - evidence of soundness, not a proof of it."
    ),
    "packages": [],
}


def imp(a, b):
    """The formula a -> b."""
    return ("->", a, b)


def show(f):
    """Readable form of a formula."""
    if isinstance(f, str):
        return f
    return f"({show(f[1])} -> {show(f[2])})"


def axiom(name, *args):
    """Instance of axiom scheme K (two arguments) or S (three arguments)."""
    if name == "K" and len(args) == 2:
        a, b = args
        return imp(a, imp(b, a))
    if name == "S" and len(args) == 3:
        a, b, c = args
        return imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
    raise ValueError(f"unknown axiom {name} with {len(args)} arguments")


def derive(proof):
    """Formulas proved by each line; returns (lines, None) or (lines, error).

    A step is ("K", A, B), ("S", A, B, C), or ("MP", i, j): from line i
    (a formula A) and line j (the formula A -> B), conclude B.
    """
    lines = []
    for n, step in enumerate(proof, start=1):
        if step[0] in ("K", "S"):
            lines.append(axiom(*step))
        elif step[0] == "MP":
            i, j = step[1], step[2]
            if not (1 <= i < n and 1 <= j < n):
                return lines, f"line {n}: refers to a line not yet proved"
            a, ab = lines[i - 1], lines[j - 1]
            if isinstance(ab, str) or ab[1] != a:
                return lines, (f"line {n}: line {j} does not have the form"
                               f" (line {i}) -> ...")
            lines.append(ab[2])
        else:
            return lines, f"line {n}: unknown rule {step[0]!r}"
    return lines, None


def check(proof, goal):
    """Check that `proof` is a correct proof of `goal`: (True, '') or (False, reason)."""
    lines, error = derive(proof)
    if error:
        return False, error
    if not lines or lines[-1] != goal:
        return False, "the last line is not the goal"
    return True, ""


def atoms(f):
    """The set of propositional variables in a formula."""
    return {f} if isinstance(f, str) else atoms(f[1]) | atoms(f[2])


def evaluate(f, val):
    """Truth value of a formula under a dict of truth values."""
    if isinstance(f, str):
        return val[f]
    return (not evaluate(f[1], val)) or evaluate(f[2], val)


def is_tautology(f):
    """True if f is true under every assignment to its variables."""
    names = sorted(atoms(f))
    return all(evaluate(f, dict(zip(names, vals)))
               for vals in itertools.product([False, True], repeat=len(names)))


P_IMP_P = [
    ("S", "p", imp("p", "p"), "p"),
    ("K", "p", imp("p", "p")),
    ("MP", 2, 1),
    ("K", "p", "p"),
    ("MP", 4, 3),
]


def main():
    goal = imp("p", "p")
    print("Checking the proof of p -> p:")
    lines, _ = derive(P_IMP_P)
    for n, (step, formula) in enumerate(zip(P_IMP_P, lines), start=1):
        rule = f"MP {step[1]},{step[2]}" if step[0] == "MP" else step[0]
        print(f"  {n}. {show(formula):44s} [{rule}]")
    print("  verdict:", check(P_IMP_P, goal))
    bad = P_IMP_P[:3] + [("MP", 1, 3)]
    print("A faulty proof (modus ponens on the wrong lines):")
    print("  verdict:", check(bad, goal))
    print()
    forms = ["p", "q", imp("p", "q"), imp("q", "p")]
    instances = [axiom("K", a, b) for a in forms for b in forms]
    instances += [axiom("S", a, b, c) for a in forms for b in forms
                  for c in forms]
    print(f"Soundness evidence: {len(instances)} axiom instances checked,"
          f" all tautologies: {all(map(is_tautology, instances))}")
    print("p -> p is a tautology:", is_tautology(goal))
    print("Peirce's law ((p -> q) -> p) -> p is a tautology:",
          is_tautology(imp(imp(imp("p", "q"), "p"), "p")))
    print("(it is not provable from K and S alone: they give only")
    print("intuitionistic implicational logic)")
    print()
    print("Epistemic status: the verdicts are exact computations. The")
    print("tautology checks are exhaustive over truth assignments but cover")
    print("only the axiom instances listed, so they are evidence for the")
    print("soundness theorem, which is proved by induction on proofs.")


if __name__ == "__main__":
    main()
