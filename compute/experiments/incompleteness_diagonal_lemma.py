"""The diagonal lemma, computed: sentences that talk about their own codes.

Formulas are strings over a small alphabet, and a bijective base-k numbering
turns every string into a natural number (its Goedel number) and back. The
function diag sends the code n of a formula phi(x) to the code of phi(n), the
result of substituting phi's own code, written as a numeral, for x.

For a template phi(x) = "P(diag(x))" the sentence G = phi(code of phi) says
"P holds of the sentence numbered diag(code of phi)" - and that sentence is G
itself. We check this identity exactly, and evaluate G when P is a decidable
property of codes: G then has a definite truth value, and G <-> P(code of G).
When P is a truth predicate, evaluating G requires evaluating G: for the liar
"~True(diag(x))" no truth value is consistent, which is the heart of Tarski's
theorem.

Numerals are written in decimal as an abbreviation of S...S0. Nothing here
decides provability, so this exhibits the mechanism of self-reference, not
the incompleteness theorem itself.

Runs unchanged in the browser (Pyodide) using only the standard library.
"""

import textwrap

EXPERIMENT = {
    "id": "incompleteness_diagonal_lemma",
    "title": "The diagonal lemma, computed with Goedel numbers",
    "evidence": ["exact"],
    "lessons": ["incompleteness"],
    "summary": (
        "Goedel-numbers strings by a bijective base-k code, computes the diagonal "
        "function diag, and checks exactly that the sentence G = phi(code of phi) "
        "built from phi(x) = P(diag(x)) satisfies diag(code phi) = code G. Evaluates "
        "such fixed points for decidable P and shows that the liar sentence has no "
        "consistent truth value. Illustrates the mechanism only: no provability is "
        "computed."
    ),
    "packages": [],
}

#: The alphabet (all symbols distinct). Each formula is a string over it.
ALPHABET = "0123456789()~&|>=+*SAPdiagxyEvenLoTru"
BASE = len(ALPHABET)


def encode(text):
    """Bijective base-k Goedel number of a string (the empty string is 0)."""
    code = 0
    for ch in text:
        index = ALPHABET.find(ch)
        if index < 0:
            raise ValueError(f"symbol {ch!r} is not in the alphabet")
        code = code * BASE + index + 1
    return code


def decode(code):
    """Inverse of encode: the string whose Goedel number is ``code``."""
    if code < 0:
        raise ValueError("codes are natural numbers")
    chars = []
    while code > 0:
        code, digit = divmod(code - 1, BASE)
        chars.append(ALPHABET[digit])
    return "".join(reversed(chars))


def substitute(formula, n):
    """Replace the free variable x by the numeral of n (x is never bound here)."""
    return formula.replace("x", str(n))


def diag(code):
    """Code of the diagonalisation phi(code of phi) of the formula with this code."""
    return encode(substitute(decode(code), code))


def fixed_point(template):
    """The sentence G = phi(code of phi) for a template phi(x)."""
    return substitute(template, encode(template))


#: Decidable properties of codes that sentences may mention.
PREDICATES = {
    "Even": lambda code: code % 2 == 0,
    "Long": lambda code: len(decode(code)) > 30,
}


def parse(sentence):
    """Split "P(diag(N))" or "~P(diag(N))" into (negated, P, diag(N))."""
    negated = sentence.startswith("~")
    body = sentence[1:] if negated else sentence
    name, _, rest = body.partition("(")
    if not (rest.startswith("diag(") and rest.endswith("))")):
        raise ValueError(f"not of the form P(diag(N)): {sentence!r}")
    return negated, name, diag(int(rest[len("diag("):-2]))


def evaluate(sentence):
    """Truth value of a sentence about a decidable property of a code."""
    negated, name, target = parse(sentence)
    value = PREDICATES[name](target)
    return (not value) if negated else value


def self_reference_values(sentence):
    """Truth values v consistent with a sentence "[~]True(diag(N))" about itself.

    If the sentence is about its own code, its value v must satisfy v = v
    (unnegated: both values fit) or v = not v (negated: none fits).
    """
    negated, name, target = parse(sentence)
    if name != "True" or target != encode(sentence):
        raise ValueError("expected a truth predicate applied to the sentence itself")
    return [v for v in (True, False) if v == ((not v) if negated else v)]


def main():
    phi = "~P(diag(x))"
    g = fixed_point(phi)
    n = encode(phi)
    print("1. Goedel's sentence, reading P(m) as 'sentence m is provable'")
    print(f"   phi(x) = {phi}; its code n has {len(str(n))} digits")
    print(f"   G = phi(n) = ~P(diag({str(n)[:10]}...)), {len(g)} symbols")
    print(f"   diag(n) == code of G: {diag(n) == encode(g)}")
    print(f"   code of G has {len(str(encode(g)))} digits, so G does not "
          f"contain it: {str(encode(g)) not in g}")
    print()
    print("2. Fixed points of decidable properties (Long = over 30 symbols)")
    for template in ["Even(diag(x))", "~Even(diag(x))", "Long(diag(x))",
                     "~Long(diag(x))"]:
        s = fixed_point(template)
        negated, name, _ = parse(s)
        value, own = evaluate(s), PREDICATES[name](encode(s))
        holds = value == ((not own) if negated else own)
        print(f"   {template:<15} G: {str(value):<5}  {name}(code G): "
              f"{str(own):<5}  equation holds: {holds}")
    print()
    print("3. A truth predicate inside the language")
    for template in ["True(diag(x))", "~True(diag(x))"]:
        values = self_reference_values(fixed_point(template))
        print(f"   {template:<15} consistent truth values for G: {values}")
    print()
    print(textwrap.fill(
        "Epistemic status: exact computation. Part 1 verifies the identity "
        "diag(code phi) = code G for one template; it holds for every template "
        "by construction, which is the diagonal lemma's proof in miniature. Part 2 "
        "checks G <-> P(code G) (or its negated form) for four fixed points. Part 3 "
        "shows only that the liar has no consistent value under this evaluation; "
        "that no arithmetical formula defines truth is Tarski's theorem, proved in "
        "the lesson. Nothing here computes provability.",
        width=78,
    ))


if __name__ == "__main__":
    main()
