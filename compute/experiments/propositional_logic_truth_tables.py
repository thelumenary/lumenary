"""Truth tables by machine: equivalences, the 16 connectives, and completeness.

A propositional formula in n variables has a truth table with 2**n rows, so
whether two formulas are equivalent can be settled by checking every row. This
experiment builds truth tables for the conditional p -> q and its converse,
inverse and contrapositive, checks De Morgan's laws and the negation of a
conditional, and then shows that every one of the 16 possible two-variable
truth tables is the table of some formula built from "not", "and" and "or"
(its disjunctive normal form), and even from NAND alone.

Unlike checking a formula about integers on many examples, checking every row
of a truth table is a complete verification: there are no other cases.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

from itertools import product

EXPERIMENT = {
    "id": "propositional_logic_truth_tables",
    "title": "Truth tables: equivalence, connectives and normal forms",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["propositional-logic"],
    "summary": (
        "Computes the truth tables of p -> q, its converse, inverse and "
        "contrapositive, checks De Morgan's laws and not(p -> q) = p and not q on "
        "every row, and builds a formula (disjunctive normal form, and a NAND-only "
        "version) for each of the 16 two-variable truth tables. Checking all rows "
        "is a complete verification for propositional formulas, provided the "
        "program itself is correct."
    ),
    "packages": [],
}


def implies(a, b):
    """The material conditional: false only when a is true and b is false."""
    return (not a) or b


def nand(a, b):
    """NAND: 'not both'."""
    return not (a and b)


def rows(n):
    """All assignments of truth values to n variables, in textbook order
    (all true first, the first variable changing slowest)."""
    if n < 0:
        raise ValueError("n must be non-negative")
    return list(product([True, False], repeat=n))


def table(formula, n):
    """The truth table of ``formula`` (a function of n booleans) as a tuple."""
    return tuple(bool(formula(*row)) for row in rows(n))


def classify(formula, n):
    """'tautology', 'contradiction' or 'contingent'."""
    values = table(formula, n)
    if all(values):
        return "tautology"
    if not any(values):
        return "contradiction"
    return "contingent"


def differing_rows(f, g, n):
    """The rows on which two formulas take different values (empty iff
    the formulas are logically equivalent)."""
    return [row for row in rows(n) if bool(f(*row)) != bool(g(*row))]


def dnf_from_table(values, names=("p", "q")):
    """A formula in disjunctive normal form with the given truth table.

    For each row where the table is true, AND together the literals that
    describe that row; then OR these terms. A table that is never true gets
    the contradiction 'p and not p'."""
    n = len(names)
    terms = []
    for row, value in zip(rows(n), values):
        if value:
            lits = [v if b else "not " + v for v, b in zip(names, row)]
            terms.append("(" + " and ".join(lits) + ")")
    if not terms:
        return f"({names[0]} and not {names[0]})"
    return " or ".join(terms)


def evaluate_dnf(text, assignment):
    """Evaluate a DNF string produced by ``dnf_from_table`` without eval()."""
    for term in text.split(" or "):
        lits = term.strip("()").split(" and ")
        ok = True
        for lit in lits:
            if lit.startswith("not "):
                ok = ok and not assignment[lit[4:]]
            else:
                ok = ok and assignment[lit]
        if ok:
            return True
    return False


def nand_only(values):
    """Build the truth function with this two-variable table using only nand,
    following the DNF: not x = x nand x, x and y = not(x nand y),
    x or y = (not x) nand (not y). Returns a function of (p, q)."""
    def neg(x):
        return nand(x, x)

    def conj(x, y):
        return neg(nand(x, y))

    def disj(x, y):
        return nand(neg(x), neg(y))

    def f(p, q):
        result = conj(p, neg(p))                     # start from "false"
        for (a, b), value in zip(rows(2), values):
            if value:
                lit_p = p if a else neg(p)
                lit_q = q if b else neg(q)
                result = disj(result, conj(lit_p, lit_q))
        return result
    return f


def main():
    tf = {True: "T", False: "F"}
    forms = [
        ("p -> q", lambda p, q: implies(p, q)),
        ("converse q -> p", lambda p, q: implies(q, p)),
        ("inverse ~p -> ~q", lambda p, q: implies(not p, not q)),
        ("contrapositive ~q -> ~p", lambda p, q: implies(not q, not p)),
    ]
    print("p q | " + " | ".join(name for name, _ in forms))
    for p, q in rows(2):
        cells = [tf[f(p, q)].center(len(name)) for name, f in forms]
        print((f"{tf[p]} {tf[q]} | " + " | ".join(cells)).rstrip())
    print()
    cond = forms[0][1]
    for name, f in forms[1:]:
        diff = differing_rows(cond, f, 2)
        shown = ", ".join(tf[a] + tf[b] for a, b in diff)
        verdict = "equivalent" if not diff else f"differs in rows {shown}"
        print(f"p -> q versus {name}: {verdict}")
    checks = [
        ("~(p & q) = ~p | ~q", lambda p, q: (not (p and q)) == ((not p) or (not q))),
        ("~(p | q) = ~p & ~q", lambda p, q: (not (p or q)) == ((not p) and (not q))),
        ("~(p -> q) = p & ~q", lambda p, q: (not implies(p, q)) == (p and not q)),
    ]
    for name, f in checks:
        print(f"{name:22} is a {classify(f, 2)}")
    print()
    tables = list(product([True, False], repeat=4))
    dnf_ok = sum(
        table(lambda p, q, t=t: evaluate_dnf(dnf_from_table(t),
                                             {"p": p, "q": q}), 2) == t
        for t in tables)
    nand_ok = sum(table(nand_only(t), 2) == t for t in tables)
    print(f"Two-variable truth tables: {len(tables)} = 2^(2^2)")
    print(f"  rebuilt from not/and/or (DNF): {dnf_ok} of {len(tables)}")
    print(f"  rebuilt from NAND alone:       {nand_ok} of {len(tables)}")
    print("  e.g. exclusive or: " + dnf_from_table((False, True, True, False)))
    print("Truth tables in n variables: " + ", ".join(
        f"n={n}: {2 ** 2 ** n}" for n in range(1, 5)))
    print()
    print("Epistemic status: every row of every table was checked, so these")
    print("equivalences and constructions are verified completely (assuming")
    print("this short program is correct). For propositional formulas a truth")
    print("table is a proof; the lesson explains why the DNF method works for")
    print("any number of variables, which no finite run can show.")


if __name__ == "__main__":
    main()
