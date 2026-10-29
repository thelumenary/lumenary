"""A tiny proof checker for addition of natural numbers.

Lean's kernel is a small program that checks every step of a proof. This
experiment builds a toy version for one theory: natural numbers written with
0 and S (successor, "plus one"), and the two defining rules of addition,
  A1:  a + 0 = a          A2:  a + S(b) = S(a + b).
A proof is a chain of terms; each step must rewrite exactly one subterm with
one rule (or with a hypothesis, such as an induction hypothesis). The checker
accepts a proof of 2 + 2 = 4, rejects a bogus one, shows why n + 0 = n is
"true by computation" while 0 + n = n gets stuck, and checks both cases of
the induction proof of 0 + n = n. Every verdict is exact; the toy shows how
checking works, but is far simpler than Lean's kernel.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "intro_lean_mini_checker",
    "title": "A toy proof checker for natural-number addition",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["intro-lean"],
    "summary": (
        "Implements a checker for equational proofs from the rules a + 0 = a "
        "and a + S(b) = S(a + b): it accepts 2 + 2 = 4, rejects a wrong step, "
        "finds that 0 + n is stuck when n is a variable (so induction is "
        "needed), checks 0 + k = k by computation for k up to 100, and checks "
        "both cases of the induction proof."
    ),
    "packages": [],
}

ZERO = ("0",)


def S(t):
    """The successor S(t), meaning t + 1."""
    return ("S", t)


def add(a, b):
    """The term a + b."""
    return ("+", a, b)


def var(name):
    """A variable such as n (an unknown natural number)."""
    return ("var", name)


def num(k):
    """The numeral k written as S(S(...S(0)...))."""
    t = ZERO
    for _ in range(k):
        t = S(t)
    return t


def show(t, top=True):
    """Write a term readably: numerals as digits, S(x) for other successors."""
    k, u = 0, t
    while u[0] == "S":
        k, u = k + 1, u[1]
    if u == ZERO:
        return str(k)
    if t[0] == "S":
        return f"S({show(t[1])})"
    if t[0] == "+":
        text = f"{show(t[1], False)} + {show(t[2], False)}"
        return text if top else f"({text})"
    return t[1]


def rewrite_root(t, rules):
    """All (name, result) for rules whose left side matches t itself."""
    out = []
    if t[0] == "+" and t[2] == ZERO:
        out.append(("A1", t[1]))
    if t[0] == "+" and t[2][0] == "S":
        out.append(("A2", S(add(t[1], t[2][1]))))
    for name, (lhs, rhs) in rules.items():
        if t == lhs:
            out.append((name, rhs))
    return out


def one_step(t, rules):
    """All (name, term) reachable from t by rewriting exactly one subterm."""
    results = rewrite_root(t, rules)
    for i in range(1, len(t)):
        if isinstance(t[i], tuple):
            for name, sub in one_step(t[i], rules):
                results.append((name, t[:i] + (sub,) + t[i + 1:]))
    return results


def check_chain(chain, rules=None):
    """Check a proof chain; return (True, rule names) or (False, bad step)."""
    rules = rules or {}
    names = []
    for k, (t, u) in enumerate(zip(chain, chain[1:]), start=1):
        found = [n for n, v in one_step(t, rules) if v == u]
        found += [n + " backwards" for n, v in one_step(u, rules) if v == t]
        if not found:
            return False, k
        names.append(found[0])
    return True, names


def first_step(t):
    """The result of rewriting the outermost, leftmost A1/A2 match, or None."""
    found = rewrite_root(t, {})
    if found:
        return found[0][1]
    for i in range(1, len(t)):
        if isinstance(t[i], tuple):
            sub = first_step(t[i])
            if sub is not None:
                return t[:i] + (sub,) + t[i + 1:]
    return None


def normalize(t, limit=10_000):
    """Apply A1/A2 until no rule applies; return (normal form, steps)."""
    steps = 0
    while steps < limit:
        nxt = first_step(t)
        if nxt is None:
            return t, steps
        t, steps = nxt, steps + 1
    raise RuntimeError("no normal form within the step limit")


def verdict(result):
    """Describe the result of check_chain in words."""
    ok, info = result
    if ok:
        return f"accepted (rules: {', '.join(info)})"
    return f"REJECTED at step {info}"


def main():
    two, n = num(2), var("n")
    proof = [add(two, two), S(add(two, num(1))), S(S(add(two, ZERO))), num(4)]
    ok, names = check_chain(proof)
    print("Proof of 2 + 2 = 4:")
    for t, why in zip(proof, ["start"] + names):
        print(f"  {show(t):<16} [{why}]")
    print(f"  accepted: {ok}")
    bogus = [add(two, two), S(add(two, num(1))), num(5)]
    print(f"Bogus chain 2 + 2 -> S(2 + 1) -> 5: {verdict(check_chain(bogus))}")
    print("  (step 2 is not a single application of a rule)")
    print()
    for t in (add(n, ZERO), add(ZERO, n)):
        nf, steps = normalize(t)
        print(f"Computing {show(t)}: reaches {show(nf)} after {steps} step(s)")
    print("  0 + n is stuck: n is neither 0 nor S(something), so no rule fits.")
    good = all(normalize(add(ZERO, num(k)))[0] == num(k) for k in range(101))
    print(f"0 + k computes to k for every numeral k = 0..100: {good}")
    print()
    print("Induction proof of 0 + n = n:")
    base = check_chain([add(ZERO, ZERO), ZERO])
    print(f"  base case 0 + 0 -> 0: {verdict(base)}")
    k = var("k")
    ih = {"IH": (add(ZERO, k), k)}
    step = [add(ZERO, S(k)), S(add(ZERO, k)), S(k)]
    print("  step case, assuming IH: 0 + k = k")
    print(f"    0 + S(k) -> S(0 + k) -> S(k): {verdict(check_chain(step, ih))}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact. Each verdict is a complete mechanical check "
        "of the given chain, and the 101 numeral cases were all computed. The "
        "checker trusts the induction principle and its two rules without "
        "question, and it is a toy: Lean's kernel checks a far richer logic. "
        "Checking 0 + k for 101 numerals is evidence about 0 + n; the "
        "induction proof is what covers every n.",
        width=78,
    ))


if __name__ == "__main__":
    main()
