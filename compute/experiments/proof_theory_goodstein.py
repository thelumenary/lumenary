"""Goodstein sequences and the ordinals below epsilon_0.

Write n in hereditary base b (exponents are written in base b too, and so on),
replace every b by b + 1, subtract 1, and repeat with the next base. Goodstein
(1944) proved that every such sequence eventually reaches 0, although the
numbers first grow enormously. The proof replaces the base by omega: each term
becomes an ordinal below epsilon_0 in Cantor normal form, and these ordinals
strictly decrease - so they must reach 0, because the ordinals are well
ordered. Kirby and Paris (1982) showed that Peano arithmetic cannot prove
Goodstein's theorem: its proof needs exactly the transfinite induction up to
epsilon_0 that Gentzen used to prove the consistency of PA.

We compute the first terms of several sequences, attach the ordinal of each
term, and check that the ordinals strictly decrease along the computed terms.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "proof_theory_goodstein",
    "title": "Goodstein sequences and ordinals below epsilon_0",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["proof-theory"],
    "summary": (
        "Computes Goodstein sequences by hereditary base change, attaches to each "
        "term its ordinal below epsilon_0 (base replaced by omega, in Cantor normal "
        "form), and checks exactly that the ordinals strictly decrease along the "
        "computed terms. A finite check: termination for every n is Goodstein's "
        "theorem, which needs induction up to epsilon_0 and is unprovable in PA."
    ),
    "packages": [],
}


def hereditary(n, base):
    """Hereditary base-``base`` form of n: a list of (exponent form, digit),
    highest exponent first; each exponent form is again such a list."""
    if base < 2 or n < 0:
        raise ValueError("need base >= 2 and n >= 0")
    terms, power = [], 0
    while n:
        n, digit = divmod(n, base)
        if digit:
            terms.append((hereditary(power, base), digit))
        power += 1
    return terms[::-1]


def evaluate(form, base):
    """The number denoted by a hereditary form when the base is ``base``."""
    return sum(digit * base ** evaluate(exp, base) for exp, digit in form)


def bump(n, base):
    """Replace the base by base + 1 everywhere in the hereditary form of n."""
    return evaluate(hereditary(n, base), base + 1)


def goodstein(n, steps):
    """The first terms g_0 = n, g_1, ... (at most steps + 1 of them), with bases."""
    terms, base = [(n, 2)], 2
    while len(terms) <= steps and n > 0:
        n = bump(n, base) - 1
        base += 1
        terms.append((n, base))
    return terms


def ordinal(n, base):
    """The ordinal of n at this base: replace the base by omega.

    An ordinal below epsilon_0 is a tuple of (exponent ordinal, coefficient)
    pairs, exponents strictly decreasing; 0 is the empty tuple. Python's tuple
    order on these is exactly the ordinal order.
    """
    return tuple((ordinal_of_form(exp), digit) for exp, digit in hereditary(n, base))


def ordinal_of_form(form):
    """Convert a hereditary form to an ordinal tuple."""
    return tuple((ordinal_of_form(exp), digit) for exp, digit in form)


def show(alpha):
    """Cantor normal form as text, writing w for omega."""
    if not alpha:
        return "0"
    parts = []
    for exp, coeff in alpha:
        if not exp:
            parts.append(str(coeff))
            continue
        e = show(exp)
        if e == "1":
            power = "w"
        elif any(c in e for c in " +*"):
            power = f"w^({e})"
        else:
            power = "w^" + e
        parts.append(power if coeff == 1 else f"{power}*{coeff}")
    return " + ".join(parts)


def strictly_decreasing(terms):
    """Do the ordinals of the given (value, base) terms strictly decrease?"""
    ords = [ordinal(n, b) for n, b in terms]
    return all(a > b for a, b in zip(ords, ords[1:]))


def main():
    print("Goodstein sequence of 3 (term, base, ordinal):")
    for n, b in goodstein(3, 10):
        print(f"   {n:>3}  base {b}   {show(ordinal(n, b))}")
    print("Goodstein sequence of 4, first terms:")
    for n, b in goodstein(4, 7):
        print(f"   {n:>4}  base {b:>2}   {show(ordinal(n, b))}")
    print()
    print("Do the ordinals strictly decrease along the computed terms?")
    for start, steps in [(3, 10), (4, 2000), (5, 300), (6, 300), (19, 3)]:
        terms = goodstein(start, steps)
        digits = len(str(max(n for n, _ in terms)))
        print(f"   n = {start:>2}: {len(terms) - 1} steps, largest term has "
              f"{digits} digits, decreasing: {strictly_decreasing(terms)}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact computation of finitely many terms. That the "
        "ordinals decrease at every step, and hence that every Goodstein sequence "
        "reaches 0, is Goodstein's theorem (the sequence of 4 needs about "
        "3 * 2^402653211 steps). Its proof uses the well-ordering of the ordinals "
        "below epsilon_0, which Peano arithmetic cannot prove (Kirby-Paris).",
        width=78,
    ))


if __name__ == "__main__":
    main()
