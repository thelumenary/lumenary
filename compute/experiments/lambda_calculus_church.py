"""A small lambda-calculus interpreter: Church numerals, recursion, and loops.

Terms are written in the usual named syntax (``\\x. x`` or ``λx. x``), parsed
into de Bruijn indices, and reduced with capture-avoiding substitution. Normal
order (leftmost-outermost redex first) computes Church-numeral arithmetic,
booleans, Kleene's predecessor and a factorial defined with the fixed-point
combinator Y, counting beta-steps. Omega = (λx. x x)(λx. x x) runs out of fuel,
and K I Omega shows that the strategy matters: normal order finds the normal
form, applicative order (arguments first) never does. Every result is an exact
computation for these particular terms.
"""

import re

EXPERIMENT = {
    "id": "lambda_calculus_church",
    "title": "Church numerals, recursion and non-termination in the λ-calculus",
    "evidence": ["exact"],
    "lessons": ["lambda-calculus"],
    "summary": (
        "Parses named λ-terms into de Bruijn indices and reduces them with "
        "capture-avoiding substitution. Normal-order reduction computes Church "
        "arithmetic (2+3, 2*3, 2^3), booleans, Kleene's predecessor and 3! via "
        "the Y combinator, counting β-steps; Omega exhausts any fuel, and K I "
        "Omega normalises under normal order but not applicative order. Exact "
        "results for these terms only, not proofs of the general theorems."
    ),
    "packages": [],
}

# A term is ("var", index), ("app", function, argument) or ("lam", body).


def parse(text, defs=None):
    """Parse a named λ-term into de Bruijn form.

    Syntax: ``\\x. body`` or ``λx. body`` (abstraction extends to the right),
    application by juxtaposition (left-associative), parentheses, and names
    from ``defs`` (a dict name -> already-parsed closed term) used as macros.
    """
    defs = defs or {}
    tokens = re.findall(r"[\\λ.()]|[A-Za-z0-9_']+", text)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def take(expected=None):
        nonlocal pos
        tok = peek()
        if tok is None or (expected is not None and tok != expected):
            raise ValueError(f"expected {expected!r} at token {pos}: {text!r}")
        pos += 1
        return tok

    def term(scope):
        if peek() in ("\\", "λ"):
            take()
            name = take()
            take(".")
            return ("lam", term([name] + scope))
        result = None
        while peek() not in (None, ")"):
            arg = atom(scope)
            result = arg if result is None else ("app", result, arg)
            if peek() in ("\\", "λ"):
                arg = term(scope)
                result = ("app", result, arg)
        if result is None:
            raise ValueError(f"empty term: {text!r}")
        return result

    def atom(scope):
        tok = take()
        if tok == "(":
            inner = term(scope)
            take(")")
            return inner
        if tok in scope:
            return ("var", scope.index(tok))
        if tok in defs:
            return defs[tok]
        raise ValueError(f"unbound name {tok!r} in {text!r}")

    result = term([])
    if pos != len(tokens):
        raise ValueError(f"unexpected {peek()!r} in {text!r}")
    return result


def shift(t, d, cutoff=0):
    """Add ``d`` to every free index (those >= ``cutoff``)."""
    if t[0] == "var":
        return ("var", t[1] + d) if t[1] >= cutoff else t
    if t[0] == "app":
        return ("app", shift(t[1], d, cutoff), shift(t[2], d, cutoff))
    return ("lam", shift(t[1], d, cutoff + 1))


def subst(t, j, s):
    """Capture-avoiding substitution t[s/j]: the shift under λ avoids capture."""
    if t[0] == "var":
        return s if t[1] == j else t
    if t[0] == "app":
        return ("app", subst(t[1], j, s), subst(t[2], j, s))
    return ("lam", subst(t[1], j + 1, shift(s, 1)))


def beta(body, arg):
    """Contract the redex (λ. body) arg."""
    return shift(subst(body, 0, shift(arg, 1)), -1)


def step_normal(t):
    """One normal-order step (leftmost-outermost redex), or None if normal."""
    if t[0] == "var":
        return None
    if t[0] == "lam":
        b = step_normal(t[1])
        return None if b is None else ("lam", b)
    f, a = t[1], t[2]
    if f[0] == "lam":
        return beta(f[1], a)
    f2 = step_normal(f)
    if f2 is not None:
        return ("app", f2, a)
    a2 = step_normal(a)
    return None if a2 is None else ("app", f, a2)


def step_applicative(t):
    """One applicative-order step: reduce inside the function and argument
    first, and contract a redex only when both parts are already normal."""
    if t[0] == "var":
        return None
    if t[0] == "lam":
        b = step_applicative(t[1])
        return None if b is None else ("lam", b)
    f, a = t[1], t[2]
    f2 = step_applicative(f)
    if f2 is not None:
        return ("app", f2, a)
    a2 = step_applicative(a)
    if a2 is not None:
        return ("app", f, a2)
    return beta(f[1], a) if f[0] == "lam" else None


def normalize(t, fuel=10_000, step=step_normal):
    """Reduce until normal; return (normal form or None, steps used)."""
    for n in range(fuel):
        nxt = step(t)
        if nxt is None:
            return t, n
        t = nxt
    return None, fuel


def church(n):
    """The Church numeral λf. λx. f^n x."""
    body = ("var", 0)
    for _ in range(n):
        body = ("app", ("var", 1), body)
    return ("lam", ("lam", body))


def decode_church(t):
    """Return n if ``t`` is exactly the Church numeral n, else None."""
    if t is None or t[0] != "lam" or t[1][0] != "lam":
        return None
    body, n = t[1][1], 0
    while body[0] == "app" and body[1] == ("var", 1):
        body, n = body[2], n + 1
    return n if body == ("var", 0) else None


def standard_defs():
    """Church encodings used in the lesson, as parsed closed terms."""
    d = {"ZERO": church(0), "ONE": church(1)}
    for name, src in [
        ("TRUE", r"\x. \y. x"), ("FALSE", r"\x. \y. y"),
        ("AND", r"\p. \q. p q p"), ("OR", r"\p. \q. p p q"),
        ("NOT", r"\p. p FALSE TRUE"),
        ("PAIR", r"\a. \b. \f. f a b"),
        ("FST", r"\p. p TRUE"), ("SND", r"\p. p FALSE"),
        ("SUCC", r"\n. \f. \x. f (n f x)"),
        ("PLUS", r"\m. \n. \f. \x. m f (n f x)"),
        ("TIMES", r"\m. \n. \f. m (n f)"),
        ("EXP", r"\m. \n. n m"),
        ("ISZERO", r"\n. n (\z. FALSE) TRUE"),
        ("PRED", r"\n. FST (n (\p. PAIR (SND p) (SUCC (SND p))) "
                 r"(PAIR ZERO ZERO))"),
        ("Y", r"\f. (\x. f (x x)) (\x. f (x x))"),
        ("FACT", r"Y (\r. \n. ISZERO n ONE (TIMES n (r (PRED n))))"),
        ("OMEGA", r"(\x. x x) (\x. x x)"),
        ("I", r"\x. x"), ("K", r"\x. \y. x"),
    ]:
        d[name] = parse(src, d)
    for n in range(10):
        d[str(n)] = church(n)
    return d


def run(src, defs, step=step_normal, fuel=10_000):
    """Parse ``src`` with ``defs`` and normalize; return (term, steps)."""
    return normalize(parse(src, defs), fuel, step)


def main():
    d = standard_defs()
    print("Normal-order reduction of Church encodings (exact beta-steps)")
    for src in ["PLUS 2 3", "TIMES 2 3", "EXP 2 3", "PRED 3", "FACT 3"]:
        nf, steps = run(src, d)
        print(f"  {src:<10} ->  Church numeral {decode_church(nf)}"
              f"   ({steps} steps)")
    print()
    print("Booleans: AND p q = p q p, OR p q = p p q")
    names = {d["TRUE"]: "TRUE", d["FALSE"]: "FALSE"}
    for p in ("TRUE", "FALSE"):
        for q in ("TRUE", "FALSE"):
            a, _ = run(f"AND {p} {q}", d)
            o, _ = run(f"OR {p} {q}", d)
            print(f"  p = {p:<5}  q = {q:<5}  AND -> {names[a]:<5}"
                  f"  OR -> {names[o]}")
    print()
    omega = d["OMEGA"]
    nf, steps = normalize(omega, 1000)
    print("Omega = (λx. x x)(λx. x x)")
    print(f"  one step turns Omega into Omega again: {step_normal(omega) == omega}")
    print(f"  normal form within {steps} steps: {nf is not None}")
    nf, steps = run("K I OMEGA", d)
    print("K I Omega")
    print(f"  normal order:      normal form I after {steps} steps:"
          f" {nf == d['I']}")
    nf, steps = run("K I OMEGA", d, step=step_applicative, fuel=1000)
    print(f"  applicative order: normal form within {steps} steps:"
          f" {nf is not None}")
    print()
    print("Epistemic status: exact computations on these particular terms, "
          "checked\nby an interpreter. They illustrate, but do not prove, "
          "that Church\nnumerals compute arithmetic in general, that Omega "
          "has no normal form\n(proved in the lesson and in Lean) or that "
          "normal order always finds a\nnormal form when one exists (the "
          "standardisation theorem).")


if __name__ == "__main__":
    main()
