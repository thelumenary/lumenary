"""Ordinal arithmetic below epsilon_0, and Goodstein sequences.

Every ordinal below epsilon_0 has a Cantor normal form
w^e1*c1 + ... + w^ek*ck with e1 > ... > ek (themselves such ordinals) and
positive integer coefficients. We represent these forms as nested tuples and
implement comparison, addition and multiplication exactly, following the
recursive definitions in the lesson. The program shows that addition and
multiplication are not commutative, tests the associative and distributive
laws on random triples (left distributivity holds, right distributivity
fails), and computes Goodstein sequences, whose terms are matched with a
strictly decreasing sequence of ordinals. Evidence: exact symbolic
computation; the random tests are experiments, not proofs.
"""

import random

EXPERIMENT = {
    "id": "cardinals_ordinal_arithmetic",
    "title": "Ordinal arithmetic in Cantor normal form",
    "evidence": ["exact", "experimental", "counterexample"],
    "lessons": ["cardinals"],
    "summary": (
        "Implements ordinals below epsilon_0 in Cantor normal form with exact "
        "comparison, addition and multiplication. Shows 1 + w = w < w + 1 and "
        "2w = w < w2, tests associativity and both distributive laws on 3000 "
        "random triples (right distributivity fails), and follows Goodstein "
        "sequences alongside their strictly decreasing ordinals. The random "
        "tests are evidence; the laws are proved by transfinite induction."
    ),
    "packages": [],
}

ZERO = ()


def nat(n):
    """The finite ordinal n."""
    if n < 0:
        raise ValueError("ordinals are non-negative")
    return () if n == 0 else ((ZERO, n),)


ONE = nat(1)
OMEGA = ((ONE, 1),)


def cmp(a, b):
    """Return -1, 0 or 1 as a < b, a = b or a > b (lexicographic on terms)."""
    for (ea, ca), (eb, cb) in zip(a, b):
        c = cmp(ea, eb)
        if c:
            return c
        if ca != cb:
            return -1 if ca < cb else 1
    return (len(a) > len(b)) - (len(a) < len(b))


def add(a, b):
    """Ordinal sum a + b: terms of a below the leading exponent of b vanish."""
    if not b:
        return a
    e, c = b[0]
    higher = tuple(t for t in a if cmp(t[0], e) > 0)
    same = [t for t in a if cmp(t[0], e) == 0]
    if same:
        return higher + ((e, same[0][1] + c),) + b[1:]
    return higher + b


def mul(a, b):
    """Ordinal product a * b, term by term in b (left distributivity)."""
    if not a or not b:
        return ZERO
    lead_e, lead_c = a[0]
    result = ZERO
    for e, c in b:
        if e == ZERO:
            term = ((lead_e, lead_c * c),) + a[1:]
        else:
            term = ((add(lead_e, e), c),)
        result = add(result, term)
    return result


def fmt(a):
    """Write a Cantor normal form, e.g. w^2*3 + w + 5."""
    if not a:
        return "0"
    parts = []
    for e, c in a:
        if e == ZERO:
            parts.append(str(c))
            continue
        if e == ONE:
            base = "w"
        elif (len(e) == 1 and e[0][0] == ZERO) or e == OMEGA:
            base = f"w^{fmt(e)}"
        else:
            base = f"w^({fmt(e)})"
        parts.append(base if c == 1 else f"{base}*{c}")
    return " + ".join(parts)


def random_ordinal(rng, max_exp=2, max_coeff=3):
    """A random ordinal below w^(max_exp + 1) with small coefficients."""
    terms = []
    for e in range(max_exp, -1, -1):
        c = rng.randint(0, max_coeff)
        if c:
            terms.append((nat(e), c))
    return tuple(terms)


def law_failures(rng, trials, law):
    """Count random triples (a, b, c) for which ``law(a, b, c)`` is False."""
    bad = []
    for _ in range(trials):
        a, b, c = (random_ordinal(rng) for _ in range(3))
        if not law(a, b, c):
            bad.append((a, b, c))
    return bad


def hereditary(n, base):
    """The ordinal obtained from n in hereditary base `base` by base -> w."""
    terms, exp = [], 0
    while n:
        n, digit = divmod(n, base)
        if digit:
            terms.append((hereditary(exp, base), digit))
        exp += 1
    return tuple(reversed(terms))


def bump(n, base):
    """Replace the base by base + 1 everywhere in hereditary notation."""
    total, exp = 0, 0
    while n:
        n, digit = divmod(n, base)
        if digit:
            total += digit * (base + 1) ** bump(exp, base)
        exp += 1
    return total


def goodstein(n, steps):
    """First terms (base, value) of the Goodstein sequence starting at n."""
    out, base = [], 2
    for _ in range(steps):
        out.append((base, n))
        if n == 0:
            break
        n = bump(n, base) - 1
        base += 1
    return out


def main():
    w = OMEGA
    two = nat(2)
    print("1. Arithmetic in Cantor normal form (w = omega):")
    rows = [
        ("1 + w", add(ONE, w), "w + 1", add(w, ONE)),
        ("2 * w", mul(two, w), "w * 2", mul(w, two)),
        ("(w + 1) * 2", mul(add(w, ONE), two), "2 * (w + 1)", mul(two, add(w, ONE))),
        ("(1 + 1) * w", mul(add(ONE, ONE), w), "1*w + 1*w", add(w, w)),
    ]
    for left, x, right, y in rows:
        print(f"   {left} = {fmt(x):<11} {right} = {fmt(y):<11} equal: {x == y}")
    rng = random.Random(2024)
    laws = [
        ("(a + b) + c = a + (b + c)",
         lambda a, b, c: add(add(a, b), c) == add(a, add(b, c))),
        ("(ab)c = a(bc)", lambda a, b, c: mul(mul(a, b), c) == mul(a, mul(b, c))),
        ("a(b + c) = ab + ac",
         lambda a, b, c: mul(a, add(b, c)) == add(mul(a, b), mul(a, c))),
        ("(a + b)c = ac + bc",
         lambda a, b, c: mul(add(a, b), c) == add(mul(a, c), mul(b, c))),
        ("a + b = b + a", lambda a, b, c: add(a, b) == add(b, a)),
    ]
    print("2. 3000 random triples below w^3 for each law:")
    examples = []
    for name, law in laws:
        bad = law_failures(rng, 3000, law)
        print(f"   {name:<27}{len(bad):>5} failures")
        if bad:
            examples.append((name, bad[0]))
    name, (a, b, c) = examples[0]
    print(f"   e.g. {name} fails for a = {fmt(a)}, b = {fmt(b)}, c = {fmt(c)}:")
    print(f"   {fmt(mul(add(a, b), c))}  versus  {fmt(add(mul(a, c), mul(b, c)))}")
    print("3. Goodstein: write n in hereditary base b, change b to b + 1, subtract 1.")
    print("   n = 3:", [v for _, v in goodstein(3, 10)])
    print("   n = 4:  base  value  ordinal (base -> w)")
    seq = goodstein(4, 7)
    for base, value in seq:
        print(f"           {base:>3} {value:>6}  {fmt(hereditary(value, base))}")
    ords = [hereditary(v, b) for b, v in seq]
    falling = all(cmp(x, y) > 0 for x, y in zip(ords, ords[1:]))
    print(f"   ordinals strictly decreasing: {falling}")
    print()
    print("Epistemic status: the normal-form arithmetic is exact, and the")
    print("non-commutativity examples are genuine counterexamples. The 3000-triple")
    print("tests are only experimental evidence for associativity and left")
    print("distributivity, which are proved by transfinite induction. Goodstein's")
    print("theorem (every sequence reaches 0) follows because ordinals are")
    print("well-ordered; n = 4 takes more steps than any computer can follow.")


if __name__ == "__main__":
    main()
