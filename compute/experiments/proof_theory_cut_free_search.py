"""Cut-free proof search in a one-sided sequent calculus.

Formulas are in negation normal form: literals p_n and ~p_n, conjunctions and
disjunctions. A sequent is a list of formulas read as their disjunction. The
cut-free rules (the same calculus as the lesson's Lean file) are:
    axiom: a sequent containing p_n and ~p_n;
    or:    from |- A, B, G infer |- A | B, G;
    and:   from |- A, G and |- B, G infer |- A & B, G.
Read upwards, each rule replaces a formula by its immediate subformulas, so a
search for a cut-free proof only ever meets subformulas of the goal (the
subformula property) and always terminates. If some branch ends in literals
with no complementary pair, that branch yields a falsifying valuation: this
is the completeness proof, run as a program.

We (1) prove some classical tautologies and check the subformula property,
(2) extract a countermodel for a non-tautology, and (3) compare the sizes of
the proofs found for the identity sequent |- A*, A with two search orders.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "proof_theory_cut_free_search",
    "title": "Cut-free proof search and the subformula property",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["proof-theory"],
    "summary": (
        "Searches for cut-free proofs in a one-sided propositional sequent calculus, "
        "checks the subformula property of every proof found, extracts a falsifying "
        "valuation when the search fails, and compares proof sizes for |- A*, A under "
        "two search orders (exponential versus linear). Exact for the formulas shown; "
        "it says nothing about first-order logic or about the cost of eliminating cuts."
    ),
    "packages": [],
}


def P(n):
    """The propositional variable p_n."""
    return ("pos", n)


def N(n):
    """The negated variable ~p_n."""
    return ("neg", n)


def And(a, b):
    """Conjunction a & b."""
    return ("and", a, b)


def Or(a, b):
    """Disjunction a | b."""
    return ("or", a, b)


def dual(f):
    """The negation of f, pushed to the atoms by De Morgan's laws."""
    tag = f[0]
    if tag == "pos":
        return ("neg", f[1])
    if tag == "neg":
        return ("pos", f[1])
    if tag == "and":
        return ("or", dual(f[1]), dual(f[2]))
    return ("and", dual(f[1]), dual(f[2]))


def show(f):
    """Readable text for a formula."""
    if f[0] == "pos":
        return f"p{f[1]}"
    if f[0] == "neg":
        return f"~p{f[1]}"
    op = " & " if f[0] == "and" else " | "
    return "(" + show(f[1]) + op + show(f[2]) + ")"


def evaluate(f, valuation):
    """Truth value of f when valuation[n] is the value of p_n."""
    tag = f[0]
    if tag == "pos":
        return valuation[f[1]]
    if tag == "neg":
        return not valuation[f[1]]
    if tag == "and":
        return evaluate(f[1], valuation) and evaluate(f[2], valuation)
    return evaluate(f[1], valuation) or evaluate(f[2], valuation)


def subformulas(f):
    """The set of subformulas of f (including f)."""
    out = {f}
    if f[0] in ("and", "or"):
        out |= subformulas(f[1]) | subformulas(f[2])
    return out


def _choose(seq, strategy):
    """Index of the compound formula to decompose next, or None."""
    compound = [i for i, f in enumerate(seq) if f[0] in ("and", "or")]
    if not compound:
        return None
    if strategy == "leftmost":
        return compound[0]
    ors = [i for i in compound if seq[i][0] == "or"]
    if ors:
        return ors[0]

    def score(i):
        f = seq[i]
        return (dual(f[1]) in seq) + (dual(f[2]) in seq)

    return max(compound, key=lambda i: (score(i), -i))


def search(seq, strategy="leftmost"):
    """Return ("proof", tree) or ("countermodel", falsifying valuation).

    A tree is (rule, sequent, children). ``strategy`` is "leftmost" (decompose
    the first compound formula) or "guided" (disjunctions first, then the
    conjunction with the most conjuncts whose duals already occur).
    """
    seq = tuple(seq)
    if any(f[0] == "pos" and ("neg", f[1]) in seq for f in seq):
        return "proof", ("axiom", seq, ())
    i = _choose(seq, strategy)
    if i is None:
        atoms = {f[1] for f in seq}
        return "countermodel", {n: ("neg", n) in seq for n in sorted(atoms)}
    f, rest = seq[i], seq[:i] + seq[i + 1:]
    premises = [(f[1], f[2]) + rest] if f[0] == "or" else [(f[1],) + rest, (f[2],) + rest]
    children = []
    for premise in premises:
        kind, result = search(premise, strategy)
        if kind == "countermodel":
            return kind, result
        children.append(result)
    return "proof", (f[0], seq, tuple(children))


def size(tree):
    """Number of rule applications in a proof tree."""
    return 1 + sum(size(c) for c in tree[2])


def depth(tree):
    """Height of a proof tree."""
    return 1 + max((depth(c) for c in tree[2]), default=0)


def has_subformula_property(tree, goal):
    """Does every formula in the proof occur as a subformula of the goal?"""
    allowed = set().union(*(subformulas(f) for f in goal))
    stack = [tree]
    while stack:
        rule, seq, children = stack.pop()
        if not set(seq) <= allowed:
            return False
        stack.extend(children)
    return True


def disjunction(formulas):
    """Right-nested disjunction of a non-empty list of formulas."""
    result = formulas[-1]
    for f in reversed(formulas[:-1]):
        result = Or(f, result)
    return result


#: Classical tautologies (in negation normal form) and one non-tautology.
EXAMPLES = [
    ("excluded middle", [Or(P(0), N(0))]),
    ("De Morgan", [Or(And(N(0), N(1)), Or(P(0), P(1)))]),
    ("distributivity", [Or(dual(And(P(0), Or(P(1), P(2)))),
                           Or(And(P(0), P(1)), And(P(0), P(2))))]),
    ("Peirce's law", [Or(And(Or(N(0), P(1)), N(0)), P(0))]),
    ("not valid", [Or(P(0), And(P(1), N(0)))]),
]


def main():
    print("1. Searching for cut-free proofs, and countermodels")
    for name, goal in EXAMPLES:
        kind, result = search(goal)
        if kind == "proof":
            sub = has_subformula_property(result, goal)
            print(f"   {name:<16} proof: size {size(result):>2}, depth "
                  f"{depth(result)}, subformula property {sub}")
        else:
            falsified = not any(evaluate(f, result) for f in goal)
            values = " ".join(f"p{k}={'TF'[not v]}" for k, v in result.items())
            print(f"   {name:<16} no proof; {values} falsifies it: {falsified}")
    print("   The last goal, " + show(EXAMPLES[-1][1][0]) + ", is not a tautology.")
    print()
    print("3. Proof sizes for |- A*, A with A = (p0 & p1) | ... | (p2n-2 & p2n-1)")
    print("    n   leftmost order   guided order")
    for n in range(1, 9):
        a = disjunction([And(P(2 * i), P(2 * i + 1)) for i in range(n)])
        sizes = [size(search([dual(a), a], s)[1]) for s in ("leftmost", "guided")]
        print(f"   {n:>2}   {sizes[0]:>14}   {sizes[1]:>12}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact computation on the formulas shown. Every proof "
        "found is checked for the subformula property and the countermodel is "
        "checked against the formula. The size table shows that cut-free proof "
        "size depends on the search order (here exponential versus linear); it "
        "does not measure the cost of cut elimination, which can be far worse "
        "(non-elementary in first-order logic).",
        width=78,
    ))


if __name__ == "__main__":
    main()
