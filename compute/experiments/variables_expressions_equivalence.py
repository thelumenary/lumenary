"""Are two expressions equivalent? Testing, refuting and expanding.

Two expressions are equivalent when they agree for EVERY value of their
variables. This experiment (1) tests several pairs of expressions on a block
of integer values, reporting the first counterexample if there is one;
(2) shows how a pair can pass four tests in a row and still be different;
(3) counts exactly, on a finite grid, how often the false rule
(a + b)^2 = a^2 + b^2 happens to give the right answer; and (4) asks SymPy to
expand the difference of each pair. Tests can refute an equivalence with one
counterexample; passing tests is evidence only. The symbolic expansion is a
genuine verification for polynomials, as trustworthy as SymPy's
implementation of the laws of algebra.
"""

import sympy

EXPERIMENT = {
    "id": "variables_expressions_equivalence",
    "title": "Equivalent expressions: tests, counterexamples and expansion",
    "evidence": ["counterexample", "exhaustive-finite", "symbolic"],
    "lessons": ["variables-expressions"],
    "summary": (
        "Tests pairs of expressions such as 4 + 3(n - 1) and 3n + 1, or "
        "(a + b)^2 and a^2 + b^2, on blocks of integers and reports the first "
        "counterexample; shows a pair that passes four tests yet differs; "
        "counts exactly how often the false square rule happens to work on a "
        "grid; and lets SymPy expand each difference. Counterexamples refute; "
        "passing tests is only evidence; the symbolic expansion is a check of "
        "the identity itself, relying on SymPy's algebra."
    ),
    "packages": ["sympy"],
}

a, b, n, x = sympy.symbols("a b n x")

#: (name, left expression, right expression) - each pair is tested below.
PAIRS = [
    ("4 + 3(n - 1)  vs  3n + 1", 4 + 3 * (n - 1), 3 * n + 1),
    ("4n - (n - 1)  vs  3n + 1", 4 * n - (n - 1), 3 * n + 1),
    ("(a + b)^2  vs  a^2 + b^2", (a + b) ** 2, a ** 2 + b ** 2),
    ("(a + b)^2  vs  a^2 + 2ab + b^2", (a + b) ** 2, a ** 2 + 2 * a * b + b ** 2),
    ("2x  vs  x^2", 2 * x, x ** 2),
]

#: The pair that agrees at x = 0, 1, 2, 3 but is not equivalent.
TRAP = (x + x * (x - 1) * (x - 2) * (x - 3), x)


def value(expr, assignment):
    """Exact value of a SymPy expression for a dict {symbol: integer}."""
    return int(expr.subs(assignment))


def ordered_values(radius):
    """The integers -radius..radius in the order 0, 1, -1, 2, -2, ..."""
    if radius < 0:
        raise ValueError("radius must be non-negative")
    out = [0]
    for k in range(1, radius + 1):
        out += [k, -k]
    return out


def assignments(variables, radius):
    """All ways to give each variable a value in -radius..radius.

    The variables are taken in alphabetical order and the values in the
    order of ``ordered_values``, so small values are tried first.
    """
    out = [{}]
    for var in sorted(variables, key=str):
        out = [{**d, var: k} for d in out for k in ordered_values(radius)]
    return out


def first_counterexample(lhs, rhs, radius):
    """Return (tests run, first assignment where lhs != rhs, or None)."""
    variables = lhs.free_symbols | rhs.free_symbols
    tests = assignments(variables, radius)
    for k, assignment in enumerate(tests, start=1):
        if value(lhs, assignment) != value(rhs, assignment):
            return k, assignment
    return len(tests), None


def symbolic_difference(lhs, rhs):
    """SymPy's expansion of lhs - rhs (0 exactly when they are identical)."""
    return sympy.expand(lhs - rhs)


def agreement_count(radius):
    """Count grid points (a, b) in -radius..radius where (a+b)^2 = a^2 + b^2.

    Uses plain integer arithmetic. By the lesson's theorem this happens
    exactly when a = 0 or b = 0, i.e. at 2(2r + 1) - 1 points.
    """
    values = range(-radius, radius + 1)
    hits = sum(1 for p in values for q in values
               if (p + q) ** 2 == p ** 2 + q ** 2)
    return hits, len(values) ** 2


def describe(assignment):
    """Readable form of an assignment such as 'a = -3, b = -3'."""
    return ", ".join(f"{k} = {v}" for k, v in
                     sorted(assignment.items(), key=lambda kv: str(kv[0])))


def main():
    print("1. Testing pairs on the values 0, 1, -1, 2, -2, 3, -3 until one fails")
    for name, lhs, rhs in PAIRS:
        tests, bad = first_counterexample(lhs, rhs, 3)
        verdict = "all agree" if bad is None else "differ at " + describe(bad)
        print(f"   {name:<31} {tests:>2} test(s): {verdict}")
    print()
    print("2. A pair that passes four tests:  x + x(x-1)(x-2)(x-3)  vs  x")
    lhs, rhs = TRAP
    for k in range(6):
        left, right = value(lhs, {x: k}), value(rhs, {x: k})
        mark = "agree" if left == right else "DIFFER"
        print(f"   x = {k}:  {left:>4}  vs  {right}   {mark}")
    print()
    hits, total = agreement_count(100)
    print("3. (a + b)^2 = a^2 + b^2 on the grid -100..100 (every point checked):")
    print(f"   true at {hits} of {total} points ({100 * hits / total:.2f}%),")
    print("   exactly the points where a = 0 or b = 0.")
    print()
    print("4. SymPy expands  left - right  (0 means identical polynomials)")
    for name, lhs, rhs in PAIRS + [("x + x(x-1)(x-2)(x-3)  vs  x", *TRAP)]:
        diff = str(symbolic_difference(lhs, rhs)).replace("**", "^")
        print(f"   {name:<31} {diff}")
    print()
    print("Epistemic status: parts 1 and 2 are finite tests - a single")
    print("counterexample refutes an equivalence, but passing tests proves")
    print("nothing (part 2 passes four in a row). Part 3 is an exhaustive count")
    print("over a finite grid only. Part 4 is a symbolic verification for these")
    print("polynomials, as reliable as SymPy's built-in algebra; the lesson's")
    print("proofs from the distributive law explain why the identities hold.")


if __name__ == "__main__":
    main()
