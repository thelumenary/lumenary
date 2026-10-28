"""Why is a negative times a negative positive? Three kinds of evidence.

1. Experimental: check (-a)(-b) = ab on a grid of integers.
2. Symbolic: let SymPy manipulate the letters a and b themselves.
3. Explanation: the lesson's proof from the distributive law, whose steps we
   display (SymPy cannot tell you *why* - it already has the rules built in).

Runs in the browser (Pyodide) with the ``sympy`` package loaded.
"""

import textwrap

import sympy

EXPERIMENT = {
    "id": "sign_rules",
    "title": "Negative times negative: grid, symbols and proof",
    "evidence": ["experimental", "symbolic"],
    "lessons": ["integers"],
    "summary": (
        "Checks (-a)(-b) = ab and (-a)b = -(ab) on a 21 x 21 grid of integers "
        "(evidence for those cases only), then lets SymPy confirm the identities "
        "symbolically, which relies on the ring rules SymPy has built in. Neither "
        "explains why the rule holds: the lesson's proof from the distributive law does."
    ),
    "packages": ["sympy"],
}


def grid(radius):
    """Return all integer pairs (a, b) with -radius <= a, b <= radius."""
    if radius < 0:
        raise ValueError("radius must be non-negative")
    values = range(-radius, radius + 1)
    return [(a, b) for a in values for b in values]


def check_on_grid(rule, pairs):
    """Apply ``rule(a, b) -> bool`` to every pair; return (cases, list of failing pairs)."""
    failures = [(a, b) for a, b in pairs if not rule(a, b)]
    return len(pairs), failures


def neg_times_neg(a, b):
    """The rule (-a)(-b) = ab for one pair of numbers."""
    return (-a) * (-b) == a * b


def neg_times_pos(a, b):
    """The rule (-a)b = -(ab) for one pair of numbers."""
    return (-a) * b == -(a * b)


def symbolic_difference(lhs, rhs):
    """Return ``sympy.expand(lhs - rhs)``; it is 0 exactly when SymPy proves lhs = rhs as polynomials."""
    return sympy.expand(lhs - rhs)


def symbolic_examples():
    """Return a list of (description, SymPy result) rows used in the printout."""
    a, b = sympy.symbols("a b")
    A, B = sympy.symbols("A B", commutative=False)
    return [
        ("(-a)*(-b)", (-a) * (-b)),
        ("(-a)*(-b) - a*b, expanded", symbolic_difference((-a) * (-b), a * b)),
        ("(-a)*b + a*b, expanded", symbolic_difference((-a) * b, -(a * b))),
        ("(a - b)*(a + b), expanded", sympy.expand((a - b) * (a + b))),
        ("how SymPy stores -a", sympy.srepr(-a)),
        ("(-A)*(-B), non-commuting A, B", (-A) * (-B)),
        ("A*B - B*A, non-commuting A, B", sympy.expand(A * B - B * A)),
    ]


#: Steps of the proof in the lesson. Each uses one ring law.
PROOF_STEPS = [
    ("0 = (-a) * 0", "x * 0 = 0, itself proved from distributivity"),
    ("  = (-a) * (b + (-b))", "b + (-b) = 0"),
    ("  = (-a)b + (-a)(-b)", "distributive law"),
    ("  = -(ab) + (-a)(-b)", "(-a)b = -(ab), proved the same way"),
    ("so (-a)(-b) = ab", "add ab to both sides"),
]


def main():
    print(f"1. Experiment: exact integer arithmetic on a grid (SymPy {sympy.__version__} used below)")
    pairs = grid(10)
    for label, rule in [("(-a)(-b) = ab   ", neg_times_neg), ("(-a)b  = -(ab)  ", neg_times_pos)]:
        cases, failures = check_on_grid(rule, pairs)
        print(f"   {label} for all a, b in -10..10: {cases} cases, {len(failures)} failures")
    print("   A grid can never reach every integer: this is evidence, not proof.")
    print()
    print("2. Symbolic algebra: SymPy works with the letters themselves")
    for description, result in symbolic_examples():
        print(f"   {description:<34} -> {result}")
    print(textwrap.fill(
        "SymPy turns (-a)*(-b) into a*b the moment it is typed: it stores -a as "
        "(-1)*a and multiplies the coefficients (-1)*(-1) = 1. A zero difference "
        "means the identity holds for all values in any commutative ring - "
        "provided SymPy's built-in rules are implemented correctly. The last two "
        "rows show the sign rule does not even need commutativity.",
        width=78, initial_indent="   ", subsequent_indent="   ",
    ))
    print()
    print("3. Why it is true (the lesson's proof, using only the ring laws):")
    for step, reason in PROOF_STEPS:
        print(f"   {step:<24} [{reason}]")
    print()
    print(textwrap.fill(
        "Epistemic status: part 1 is experimental evidence for 441 cases; part 2 "
        "is a symbolic verification that is only as trustworthy as SymPy's "
        "implementation of the ring axioms; only the proof in part 3 explains "
        "why (-a)(-b) = ab in every ring.",
        width=78,
    ))


if __name__ == "__main__":
    main()
