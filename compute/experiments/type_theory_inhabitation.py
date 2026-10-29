"""Which tautologies are inhabited types? Truth tables versus proof search.

Under the Curry-Howard correspondence a propositional formula is a type, and
it has a closed λ-term exactly when it is provable in intuitionistic logic.
Truth tables decide *classical* validity. Intuitionistic provability is
decided by Dyckhoff's contraction-free sequent calculus G4ip (1992), whose
proof search always terminates. We compare the two on famous formulas
(Peirce's law, excluded middle, De Morgan), check Glivenko's theorem (a
classical tautology A always has an intuitionistic proof of ¬¬A), and survey
every implicational formula with at most four atoms over p, q. These are
exact decisions for the formulas listed, relying on the correctness of the
two decision procedures.
"""

import itertools
import re

EXPERIMENT = {
    "id": "type_theory_inhabitation",
    "title": "Inhabited types versus tautologies: proof search and truth tables",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["type-theory"],
    "summary": (
        "Decides classical validity by truth tables and intuitionistic "
        "provability (= inhabitation of the corresponding type) by Dyckhoff's "
        "terminating calculus G4ip, for famous formulas such as Peirce's law, "
        "excluded middle and De Morgan's laws, checks Glivenko's theorem on "
        "them, and surveys all 102 implicational formulas with at most four "
        "atoms over p, q. Exact for these formulas, given correct procedures."
    ),
    "packages": [],
}

BOT = ("bot",)


def parse(text):
    """Parse a formula: atoms are lowercase letters, ``~`` is negation
    (A -> bot), then ``&``, ``|`` and right-associative ``->``."""
    tokens = re.findall(r"->|[a-z]|[~&|()]|_\|_", text)
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def take():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError(f"unexpected end of {text!r}")
        pos += 1
        return tokens[pos - 1]

    def imp():
        left = disj()
        if peek() == "->":
            take()
            return ("imp", left, imp())
        return left

    def disj():
        left = conj()
        while peek() == "|":
            take()
            left = ("or", left, conj())
        return left

    def conj():
        left = unary()
        while peek() == "&":
            take()
            left = ("and", left, unary())
        return left

    def unary():
        tok = take()
        if tok == "~":
            return ("imp", unary(), BOT)
        if tok == "(":
            inner = imp()
            if take() != ")":
                raise ValueError(f"missing ')' in {text!r}")
            return inner
        if tok == "_|_":
            return BOT
        if re.fullmatch(r"[a-z]", tok):
            return ("atom", tok)
        raise ValueError(f"unexpected {tok!r} in {text!r}")

    result = imp()
    if pos != len(tokens):
        raise ValueError(f"trailing input in {text!r}")
    return result


def atoms(f):
    """The set of atom names in a formula."""
    if f[0] == "atom":
        return {f[1]}
    if f == BOT:
        return set()
    return atoms(f[1]) | atoms(f[2])


def evaluate(f, v):
    """Truth value of ``f`` under the assignment ``v`` (dict atom -> bool)."""
    kind = f[0]
    if kind == "atom":
        return v[f[1]]
    if kind == "bot":
        return False
    a, b = evaluate(f[1], v), evaluate(f[2], v)
    return {"imp": (not a) or b, "and": a and b, "or": a or b}[kind]


def tautology(f):
    """Classical validity, by checking every row of the truth table."""
    names = sorted(atoms(f))
    return all(evaluate(f, dict(zip(names, row)))
               for row in itertools.product([True, False], repeat=len(names)))


def provable(goal, context=frozenset(), _memo=None):
    """Intuitionistic provability of ``context ⊢ goal`` by G4ip proof search.

    Invertible rules are applied eagerly; the two non-invertible rules (choose
    a disjunct on the right, or use a hypothesis (C -> D) -> B) are tried in
    every possible way. Dyckhoff (1992) proved that this search terminates
    and is complete for intuitionistic propositional logic.
    """
    memo = {} if _memo is None else _memo
    key = (context, goal)
    if key in memo:
        return memo[key]
    memo[key] = False  # guards against re-entry; G4ip never loops anyway
    result = _search(context, goal, memo)
    memo[key] = result
    return result


def _search(ctx, goal, memo):
    if BOT in ctx or goal in ctx:
        return True
    for f in ctx:
        rest = ctx - {f}
        if f[0] == "and":
            return provable(goal, rest | {f[1], f[2]}, memo)
        if f[0] == "or":
            return (provable(goal, rest | {f[1]}, memo)
                    and provable(goal, rest | {f[2]}, memo))
        if f[0] == "imp":
            a, b = f[1], f[2]
            if a == BOT:
                return provable(goal, rest, memo)
            if a[0] == "atom" and a in ctx:
                return provable(goal, rest | {b}, memo)
            if a[0] == "and":
                return provable(goal, rest | {("imp", a[1], ("imp", a[2], b))}, memo)
            if a[0] == "or":
                return provable(goal, rest | {("imp", a[1], b), ("imp", a[2], b)},
                                memo)
    if goal[0] == "imp":
        return provable(goal[2], ctx | {goal[1]}, memo)
    if goal[0] == "and":
        return provable(goal[1], ctx, memo) and provable(goal[2], ctx, memo)
    if goal[0] == "or" and (provable(goal[1], ctx, memo)
                            or provable(goal[2], ctx, memo)):
        return True
    for f in ctx:
        if f[0] == "imp" and f[1][0] == "imp":
            c, d, b = f[1][1], f[1][2], f[2]
            rest = ctx - {f}
            if (provable(("imp", c, d), rest | {("imp", d, b)}, memo)
                    and provable(goal, rest | {b}, memo)):
                return True
    return False


def implicational_formulas(max_atoms, names=("p", "q")):
    """Every implicational formula with 1..max_atoms atom occurrences."""
    by_size = {1: [("atom", n) for n in names]}
    for k in range(2, max_atoms + 1):
        by_size[k] = [("imp", a, b)
                      for left in range(1, k)
                      for a in by_size[left] for b in by_size[k - left]]
    return [f for k in range(1, max_atoms + 1) for f in by_size[k]]


def show(f):
    """Print a formula with minimal brackets."""
    if f[0] == "atom":
        return f[1]
    if f == BOT:
        return "⊥"
    if f[0] == "imp" and f[2] == BOT:
        inner = show(f[1])
        return "¬" + (inner if f[1][0] == "atom" or f[1][2] == BOT
                      else f"({inner})")
    op = {"imp": " → ", "and": " ∧ ", "or": " ∨ "}[f[0]]
    left = show(f[1])
    if f[1][0] not in ("atom", "bot") and not (f[1][0] == "imp" and f[1][2] == BOT):
        left = f"({left})"
    right = show(f[2])
    if f[0] != "imp" and f[2][0] not in ("atom", "bot") and not (
            f[2][0] == "imp" and f[2][2] == BOT):
        right = f"({right})"
    return left + op + right


FAMOUS = [
    ("K combinator", "p -> q -> p"),
    ("S combinator", "(p -> q -> r) -> (p -> q) -> p -> r"),
    ("Peirce's law", "((p -> q) -> p) -> p"),
    ("double negation elim.", "~~p -> p"),
    ("double negation intro.", "p -> ~~p"),
    ("triple negation", "~~~p -> ~p"),
    ("excluded middle", "p | ~p"),
    ("¬¬ excluded middle", "~~(p | ~p)"),
    ("contraposition", "(p -> q) -> ~q -> ~p"),
    ("converse contraposition", "(~q -> ~p) -> p -> q"),
    ("De Morgan (∨)", "~(p | q) -> ~p & ~q"),
    ("De Morgan (∧)", "~(p & q) -> ~p | ~q"),
    ("Dummett's axiom", "(p -> q) | (q -> p)"),
    ("affirming the consequent", "(p -> q) -> q -> p"),
]


def main():
    print(f"{'formula':<31}{'classical':>10}{'inhabited':>11}   name")
    tautologies = []
    for name, src in FAMOUS:
        f = parse(src)
        taut, prov = tautology(f), provable(f)
        if taut:
            tautologies.append(f)
        print(f"{show(f):<31}{'yes' if taut else 'no':>10}"
              f"{'yes' if prov else 'no':>11}   {name}")
    glivenko = all(provable(("imp", ("imp", f, BOT), BOT)) for f in tautologies)
    print()
    print(f"Glivenko: ¬¬A is inhabited for all {len(tautologies)} tautologies A"
          f" above: {glivenko}")
    forms = implicational_formulas(4)
    taut = [f for f in forms if tautology(f)]
    prov = [f for f in forms if provable(f)]
    gap = [show(f) for f in taut if not provable(f)]
    print(f"All {len(forms)} formulas built from p, q, → with <= 4 atoms:")
    print(f"  {len(taut)} classical tautologies, {len(prov)} inhabited types;")
    print(f"  tautologies without a λ-term: {', '.join(gap)}")
    print()
    print("Epistemic status: exact decisions for the formulas shown, assuming "
          "the\ntruth-table check and the G4ip search are implemented "
          "correctly (G4ip\nis proved terminating and complete by Dyckhoff, "
          "1992). That Peirce's law\nhas no λ-term is proved in the lesson "
          "and in Lean by a Kripke model.")


if __name__ == "__main__":
    main()
