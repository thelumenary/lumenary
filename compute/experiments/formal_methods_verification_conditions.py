"""From Hoare logic to algebra: verification conditions for integer division.

The program r := a; q := 0; while b <= r do (r := r - b; q := q + 1) is
annotated with a loop invariant. A weakest-precondition calculus (assignment
is substitution, wp(c1; c2, Q) = wp(c1, wp(c2, Q))) turns the annotated program
into three verification conditions (VCs): plain implications between integer
formulas, with no program left in them. SymPy performs the substitutions
symbolically. Each VC is then checked twice: its equational part by symbolic
algebra (exact), and the whole implication on every integer point of a box
(exhaustive for the box only - not a proof for all integers). A deliberately
weak invariant produces a VC with a counterexample, and random testing of the
program itself is shown for contrast.
"""

import itertools
import random

import sympy

EXPERIMENT = {
    "id": "formal_methods_verification_conditions",
    "title": "Verification conditions for division by repeated subtraction",
    "evidence": ["symbolic", "exhaustive-finite", "counterexample"],
    "lessons": ["formal-methods"],
    "summary": (
        "Generates the verification conditions of a loop program from a "
        "weakest-precondition calculus, with SymPy doing the substitutions. The "
        "equational part of each condition is checked symbolically and the whole "
        "implication on every point of a box of integers (evidence for the box "
        "only). A too-weak invariant yields a condition with a counterexample, and "
        "random tests of the program are shown for contrast."
    ),
    "packages": ["sympy"],
}

a, b, q, r = sympy.symbols("a b q r", integer=True)
VARS = (a, b, q, r)

PRE = sympy.And(a >= 0, b > 0)
POST = sympy.And(sympy.Eq(a, q * b + r), r >= 0, r < b)
GOOD_INV = sympy.And(sympy.Eq(a, q * b + r), r >= 0, b > 0)
WEAK_INV = sympy.And(sympy.Eq(a, q * b + r), b > 0)        # forgets r >= 0
GUARD = b <= r
BODY = [(r, r - b), (q, q + 1)]                            # r := r-b; q := q+1
INIT = [(r, a), (q, sympy.Integer(0))]                     # r := a; q := 0


def wp_assignments(assignments, post):
    """Weakest precondition of a sequence of assignments: substitute backwards."""
    for var, expr in reversed(assignments):
        post = post.subs(var, expr, simultaneous=True)
    return post


def verification_conditions(inv):
    """The three VCs (name, hypothesis, conclusion) for the annotated program."""
    return [
        ("entry", PRE, wp_assignments(INIT, inv)),
        ("preservation", sympy.And(inv, GUARD), wp_assignments(BODY, inv)),
        ("exit", sympy.And(inv, sympy.Not(GUARD)), POST),
    ]


def equations_reduce(hyp, concl):
    """Do the equations in ``concl`` follow from a = q*b + r by algebra alone?"""
    eqs = [c for c in sympy.And.make_args(concl) if isinstance(c, sympy.Eq)]
    return all(sympy.expand((e.lhs - e.rhs).subs(a, q * b + r)) == 0
               for e in eqs)


def box_counterexample(hyp, concl, radius):
    """First integer point in [-radius, radius]^4 where hyp holds and concl fails."""
    holds_hyp = sympy.lambdify(VARS, hyp, modules="math")
    holds_concl = sympy.lambdify(VARS, concl, modules="math")
    rng = range(-radius, radius + 1)
    for point in itertools.product(rng, repeat=4):
        if holds_hyp(*point) and not holds_concl(*point):
            return point
    return None


def fmt(formula):
    """Compact text for a conjunction of (in)equalities, e.g. 'a = b*q + r, r >= 0'."""
    parts = []
    for c in sympy.And.make_args(formula):
        op = "=" if isinstance(c, sympy.Eq) else c.rel_op
        parts.append(f"{sympy.sstr(c.lhs)} {op} {sympy.sstr(c.rhs)}")
    return ", ".join(parts)


def run_program(a0, b0):
    """Execute the program directly; return (q, r)."""
    r0, q0 = a0, 0
    while b0 <= r0:
        r0, q0 = r0 - b0, q0 + 1
    return q0, r0


def random_tests(n, seed=2024):
    """Run the program on n random inputs with a >= 0, b > 0; count failures."""
    rng = random.Random(seed)
    failures = 0
    for _ in range(n):
        a0, b0 = rng.randint(0, 10**4), rng.randint(1, 100)
        q0, r0 = run_program(a0, b0)
        failures += not (a0 == q0 * b0 + r0 and 0 <= r0 < b0)
    return failures


def main():
    radius = 4
    print("Program: r := a; q := 0; while b <= r do (r := r - b; q := q + 1)")
    print("Pre: a >= 0, b > 0.   Post: a = q*b + r, r >= 0, r < b.")
    for label, inv in [("I", GOOD_INV), ("weak I (no r >= 0)", WEAK_INV)]:
        print()
        print(f"{label}: {fmt(inv)}")
        names = {"entry": "Pre ==> wp(r := a; q := 0, I):",
                 "preservation": "I, b <= r ==> wp(body, I):",
                 "exit": "I, b > r ==> Post:"}
        for name, hyp, concl in verification_conditions(inv):
            alg = "yes" if equations_reduce(hyp, concl) else "no"
            cex = box_counterexample(hyp, concl, radius)
            box = "none" if cex is None else "(a, b, q, r) = " + str(cex)
            print(f"  VC {name}: {names[name]}")
            print(f"     {fmt(concl)}")
            print(f"     algebra: {alg}; counterexample in box: {box}")
    print()
    print(f"Box = all {(2 * radius + 1) ** 4} integer points of "
          f"[-{radius}, {radius}]^4.")
    print(f"Random tests of the program itself: 2000 runs, "
          f"{random_tests(2000)} failures.")
    print()
    print("Epistemic status: the substitutions and the algebraic reductions are")
    print("exact symbolic computations; the box search is exhaustive only on the")
    print("box and the random tests cover 2000 inputs, so neither proves the VCs")
    print("for all integers (the inequalities follow by linear arithmetic, as in")
    print("the Lean proof div_correct). The weak invariant's failed VC refutes")
    print("that proof attempt, not the program, which is correct.")


if __name__ == "__main__":
    main()
