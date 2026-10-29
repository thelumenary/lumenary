"""Is an operation on equivalence classes well defined? Test every representative.

Integers are built as classes of pairs (a, b) of naturals with
(a, b) ~ (c, d) iff a + d = c + b, and fractions as classes of pairs (a, b)
with b != 0 and (a, b) ~ (c, d) iff ad = cb. An operation on pairs defines an
operation on classes only if equivalent inputs always give equivalent outputs.
The experiment checks this exhaustively for small pairs: the lesson's addition
and multiplication pass, while two tempting rules - "multiply componentwise"
for integer pairs and the "mediant" (a + c)/(b + d) for fractions - fail, and
it prints a counterexample for each. It also shows "fractions" over Z/6Z
breaking transitivity. Exhaustive for small cases; the general claims are
the lesson's proofs.
"""

import itertools

EXPERIMENT = {
    "id": "number_system_constructions_well_defined",
    "title": "Well-definedness tested on every small representative",
    "evidence": ["exhaustive-finite", "counterexample"],
    "lessons": ["number-system-constructions"],
    "summary": (
        "For integer pairs (a, b) ~ (c, d) iff a + d = c + b, and fraction pairs "
        "(a, b) ~ (c, d) iff ad = cb, checks every small choice of representatives: "
        "the lesson's addition and multiplication respect the relations; the "
        "componentwise product of integer pairs and the mediant of fractions do "
        "not (counterexamples printed). Also shows fraction equality over Z/6Z "
        "failing to be transitive."
    ),
    "packages": [],
}

N = range(7)


def int_rel(p, q):
    """(a, b) ~ (c, d) iff a + d = c + b: both stand for a - b = c - d."""
    return p[0] + q[1] == q[0] + p[1]


def int_add(p, q):
    """(a, b) + (c, d) = (a + c, b + d)."""
    return (p[0] + q[0], p[1] + q[1])


def int_mul(p, q):
    """(a, b)(c, d) = (ac + bd, ad + bc), from (a - b)(c - d)."""
    return (p[0] * q[0] + p[1] * q[1], p[0] * q[1] + p[1] * q[0])


def int_bad(p, q):
    """A tempting but wrong rule: multiply componentwise."""
    return (p[0] * q[0], p[1] * q[1])


def frac_rel(p, q):
    """(a, b) ~ (c, d) iff ad = cb."""
    return p[0] * q[1] == q[0] * p[1]


def frac_add(p, q):
    """a/b + c/d = (ad + cb)/(bd)."""
    return (p[0] * q[1] + q[0] * p[1], p[1] * q[1])


def mediant(p, q):
    """The 'freshman sum' (a + c)/(b + d)."""
    return (p[0] + q[0], p[1] + q[1])


def counterexample(pairs, rel, op):
    """First (p, p', q, q') with p ~ p', q ~ q' but op(p, q) !~ op(p', q')."""
    equiv = [(p, p2) for p in pairs for p2 in pairs if rel(p, p2)]
    for (p, p2), (q, q2) in itertools.product(equiv, repeat=2):
        if not rel(op(p, q), op(p2, q2)):
            return p, p2, q, q2
    return None


def transitivity_failure(n):
    """Pairs in Z/nZ with non-zero second entry breaking transitivity."""
    pairs = [(a, b) for a in range(n) for b in range(1, n)]

    def rel(p, q):
        return (p[0] * q[1] - q[0] * p[1]) % n == 0

    for x, y, z in itertools.product(pairs, repeat=3):
        if rel(x, y) and rel(y, z) and not rel(x, z):
            return x, y, z
    return None


def main():
    ints = [(a, b) for a in N for b in N]
    fracs = [(a, b) for a in range(0, 5) for b in range(1, 6)]
    print(f"Integer pairs (a, b) with 0 <= a, b <= 6: {len(ints)}")
    for name, op in [("(a+c, b+d)", int_add), ("(ac+bd, ad+bc)", int_mul),
                     ("(ac, bd)", int_bad)]:
        bad = counterexample(ints, int_rel, op)
        verdict = "well defined" if bad is None else f"FAILS: {bad}"
        print(f"  {name:<16}{verdict}")
    p, p2, q, q2 = counterexample(ints, int_rel, int_bad)
    print(f"  {p} ~ {p2} and {q} ~ {q2}, but the products")
    print(f"  {int_bad(p, q)} and {int_bad(p2, q2)} are not equivalent")
    print()
    print(f"Fraction pairs a/b with 0 <= a <= 4, 1 <= b <= 5: {len(fracs)}")
    for name, op in [("(ad+cb)/(bd)", frac_add), ("(a+c)/(b+d)", mediant)]:
        bad = counterexample(fracs, frac_rel, op)
        verdict = "well defined" if bad is None else f"FAILS: {bad}"
        print(f"  {name:<16}{verdict}")
    p, p2, q, q2 = counterexample(fracs, frac_rel, mediant)
    m1, m2 = mediant(p, q), mediant(p2, q2)
    print(f"  {p[0]}/{p[1]} = {p2[0]}/{p2[1]} and {q[0]}/{q[1]} = {q2[0]}/{q2[1]},"
          f" but {m1[0]}/{m1[1]} != {m2[0]}/{m2[1]}")
    print()
    for n in (5, 6):
        print(f"'Fractions' over Z/{n}Z, transitivity counterexample:",
              transitivity_failure(n))
    print()
    print("Epistemic status: exhaustive checks over small representatives, plus")
    print("explicit counterexamples. A failure found here is a proof that the")
    print("rule is not well defined; a pass is only evidence. The lesson proves")
    print("well-definedness of the correct operations for all representatives.")


if __name__ == "__main__":
    main()
