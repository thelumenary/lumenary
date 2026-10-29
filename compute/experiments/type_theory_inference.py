"""Inferring simple types: which λ-terms are proofs, and of what?

Given an untyped λ-term, we look for a simple type for it by collecting
equations between type variables and solving them by unification, as in the
Hindley-Milner algorithm (without let). If a type exists, the result is the
most general (principal) one: every other type of the term is an instance.
Read through Curry-Howard, the principal type of a closed term is the most
general formula it proves, so each one is checked to be a tautology. Terms
built on self-application, such as ω = λx. x x and the Y combinator, fail
the occurs check: no type A can equal A → B. The results are exact
computations for the terms listed.
"""

import itertools
import re

EXPERIMENT = {
    "id": "type_theory_inference",
    "title": "Type inference by unification: principal types as theorems",
    "evidence": ["exact"],
    "lessons": ["type-theory"],
    "summary": (
        "Infers principal simple types of untyped λ-terms by unification "
        "(Hindley-Milner without let): the I, K, S, B, C and W combinators, "
        "Church numerals and addition, and terms that cannot be typed, such "
        "as λx. x x and Y, which fail the occurs check. Each principal type is "
        "checked to be a classical tautology, as Curry-Howard predicts. Exact "
        "computations for these terms only."
    ),
    "packages": [],
}


def parse(text):
    """Parse a named term: ``\\x. M`` or ``λx. M``, application, brackets.
    Several binders may share one backslash: ``\\x y. M``."""
    tokens = re.findall(r"[\\λ.()]|[A-Za-z0-9_']+", text)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def take():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError(f"unexpected end of {text!r}")
        pos += 1
        return tokens[pos - 1]

    def term():
        if peek() in ("\\", "λ"):
            take()
            names = []
            while peek() != ".":
                names.append(take())
            take()
            body = term()
            for name in reversed(names):
                body = ("lam", name, body)
            return body
        result = None
        while peek() not in (None, ")"):
            arg = term() if peek() in ("\\", "λ") else atom()
            result = arg if result is None else ("app", result, arg)
        if result is None:
            raise ValueError(f"empty term in {text!r}")
        return result

    def atom():
        tok = take()
        if tok == "(":
            inner = term()
            if take() != ")":
                raise ValueError(f"missing ')' in {text!r}")
            return inner
        return ("var", tok)

    result = term()
    if pos != len(tokens):
        raise ValueError(f"trailing input in {text!r}")
    return result


class Untypable(Exception):
    """Raised when the equations have no solution."""


def resolve(t, sub):
    """Apply the substitution ``sub`` (type variable -> type) fully."""
    while t[0] == "tv" and t[1] in sub:
        t = sub[t[1]]
    if t[0] == "fn":
        return ("fn", resolve(t[1], sub), resolve(t[2], sub))
    return t


def occurs(v, t, sub):
    """Does the type variable ``v`` occur in ``t``?"""
    t = resolve(t, sub)
    if t[0] == "tv":
        return t[1] == v
    return occurs(v, t[1], sub) or occurs(v, t[2], sub)


def unify(a, b, sub):
    """Extend ``sub`` so that a and b become equal, or raise Untypable."""
    a, b = resolve(a, sub), resolve(b, sub)
    if a == b:
        return
    if a[0] == "tv":
        if occurs(a[1], b, sub):
            raise Untypable(f"occurs check: t{a[1]} = {show(b)}")
        sub[a[1]] = b
    elif b[0] == "tv":
        unify(b, a, sub)
    else:
        unify(a[1], b[1], sub)
        unify(a[2], b[2], sub)


def infer(term):
    """The principal type of a closed term, with variables renamed a, b, …
    in order of appearance; raises Untypable if there is none."""
    sub, counter = {}, itertools.count()

    def go(t, env):
        if t[0] == "var":
            if t[1] not in env:
                raise ValueError(f"free variable {t[1]}")
            return env[t[1]]
        if t[0] == "lam":
            a = ("tv", next(counter))
            return ("fn", a, go(t[2], {**env, t[1]: a}))
        f, x = go(t[1], env), go(t[2], env)
        r = ("tv", next(counter))
        unify(f, ("fn", x, r), sub)
        return r

    return rename(resolve(go(term, {}), sub))


def rename(t):
    """Rename type variables to 'a', 'b', … in order of first appearance."""
    names = {}

    def go(u):
        if u[0] == "tv":
            names.setdefault(u[1], "abcdefghijklmnopqrstuvwxyz"[len(names)])
            return ("tv", names[u[1]])
        return ("fn", go(u[1]), go(u[2]))

    return go(t)


def show(t):
    """Print a type with right-associative arrows."""
    if t[0] == "tv":
        return t[1] if isinstance(t[1], str) else f"t{t[1]}"
    left = show(t[1])
    if t[1][0] == "fn":
        left = f"({left})"
    return f"{left} → {show(t[2])}"


def tautology(t):
    """Is the type, read as a formula of implicational logic, valid?"""
    names = sorted({u[1] for u in walk(t) if u[0] == "tv"})

    def value(u, v):
        if u[0] == "tv":
            return v[u[1]]
        return (not value(u[1], v)) or value(u[2], v)

    return all(value(t, dict(zip(names, row)))
               for row in itertools.product([True, False], repeat=len(names)))


def walk(t):
    """All subtypes of a type."""
    yield t
    if t[0] == "fn":
        yield from walk(t[1])
        yield from walk(t[2])


EXAMPLES = [
    ("I", r"\x. x"),
    ("K", r"\x y. x"),
    ("S", r"\f g x. f x (g x)"),
    ("B (compose)", r"\f g x. f (g x)"),
    ("C (flip)", r"\f x y. f y x"),
    ("W", r"\f x. f x x"),
    ("K I", r"(\x y. x) (\z. z)"),
    ("Church 2", r"\f x. f (f x)"),
    ("plus", r"\m n f x. m f (n f x)"),
    ("λx. λk. k x", r"\x k. k x"),
    ("ω = λx. x x", r"\x. x x"),
    ("Y", r"\f. (\x. f (x x)) (\x. f (x x))"),
]


def main():
    print("Principal types (read as formulas: each should be a tautology)")
    for name, src in EXAMPLES:
        try:
            ty = infer(parse(src))
        except Untypable as err:
            print(f"  {name:<13} untypable ({err})")
            continue
        mark = "tautology" if tautology(ty) else "NOT a tautology"
        print(f"  {name:<13} {show(ty):<38} {mark}")
    print()
    print("Epistemic status: exact computations for these terms. Unification "
          "finds\nthe principal type whenever one exists (Hindley 1969, "
          "Milner 1978); that\nevery simply typed closed term proves a "
          "tautology is Curry-Howard plus\nsoundness, proved in the lesson. "
          "A tautology need not have a term:\nPeirce's law is the standard "
          "counterexample.")


if __name__ == "__main__":
    main()
