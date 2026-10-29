"""Class numbers of imaginary quadratic fields and units of real ones.

Gauss's reduced binary quadratic forms count ideal classes: for a negative
fundamental discriminant D, the class number h(D) of Q(sqrt D) equals the
number of reduced primitive forms a x^2 + b xy + c y^2 with b^2 - 4ac = D,
|b| <= a <= c (and b >= 0 if |b| = a or a = c). We compute h(D) this way for
every fundamental discriminant -200 <= D < 0, and check each value against
Dirichlet's analytic class number formula
    h(D) = -(w / (2|D|)) * sum_{a=1}^{|D|-1} chi_D(a) * a,
where chi_D is the Kronecker symbol and w is the number of roots of unity.
Then, for real quadratic rings Z[sqrt d], we find the fundamental unit by the
continued fraction of sqrt d (the smallest solution of x^2 - d y^2 = +-1),
showing how wildly its size varies - Dirichlet's unit theorem promises one
fundamental unit but says nothing about how large it is. Exact integer
arithmetic, exhaustive in the stated range.
"""

import math

EXPERIMENT = {
    "id": "algebraic_number_theory_class_numbers",
    "title": "Class numbers by reduced forms and fundamental units",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["algebraic-number-theory"],
    "summary": (
        "Computes the class number of every imaginary quadratic field with "
        "fundamental discriminant -200 <= D < 0 by counting Gauss's reduced "
        "forms, checks each against Dirichlet's class number formula, lists "
        "the D with class number 1, and finds fundamental units of Z[sqrt d] "
        "from continued fractions. Exact and exhaustive in that range."
    ),
    "packages": [],
}


def is_squarefree(n):
    """True if no square of a prime divides n (n != 0)."""
    n = abs(n)
    return all(n % (q * q) for q in range(2, math.isqrt(n) + 1))


def is_fundamental(D):
    """Fundamental discriminant test for D != 0, 1."""
    if D % 4 == 1:
        return is_squarefree(D)
    if D % 4 == 0:
        m = D // 4
        return m % 4 in (2, 3) and is_squarefree(m)
    return False


def reduced_forms(D):
    """Reduced primitive positive definite forms (a, b, c) of discriminant D < 0."""
    forms = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a or (c == a and b < 0):
                continue
            if math.gcd(math.gcd(a, b), c) == 1:
                forms.append((a, b, c))
        a += 1
    return forms


def class_number(D):
    """h(D) as the number of reduced primitive forms."""
    return len(reduced_forms(D))


def kronecker(D, n):
    """Kronecker symbol (D/n) for n >= 1."""
    result, m, p = 1, n, 2
    while m > 1:
        if m % p:
            p += 1
            continue
        m //= p
        if p == 2:
            factor = 0 if D % 2 == 0 else (1 if D % 8 in (1, 7) else -1)
        else:
            r = pow(D % p, (p - 1) // 2, p)
            factor = 0 if D % p == 0 else (1 if r == 1 else -1)
        result *= factor
    return result


def class_number_formula(D):
    """Dirichlet's formula h = -(w / 2|D|) sum chi_D(a) a, as an exact integer."""
    w = {-3: 6, -4: 4}.get(D, 2)
    s = sum(kronecker(D, a) * a for a in range(1, -D))
    value = -w * s
    if value % (2 * -D):
        raise ArithmeticError("formula did not give an integer")
    return value // (2 * -D)


def fundamental_unit(d):
    """Smallest x + y sqrt d (x, y > 0) with x^2 - d y^2 = +-1, d not a square."""
    a0 = math.isqrt(d)
    m, q, a = 0, 1, a0
    h_prev, h = 1, a0
    k_prev, k = 0, 1
    while h * h - d * k * k not in (1, -1):
        m = q * a - m
        q = (d - m * m) // q
        a = (a0 + m) // q
        h_prev, h = h, a * h + h_prev
        k_prev, k = k, a * k + k_prev
    return h, k, h * h - d * k * k


def main():
    discs = [D for D in range(-200, 0) if is_fundamental(D)]
    hs = {D: class_number(D) for D in discs}
    agree = all(hs[D] == class_number_formula(D) for D in discs)
    print(f"Fundamental discriminants -200 <= D < 0: {len(discs)} fields")
    print("  h(D) by reduced forms equals Dirichlet's formula for all:",
          agree)
    print("  h(D) for the first fields:")
    first = sorted(discs, reverse=True)[:20]
    for start in (0, 10):
        print("   " + " ".join(f"{D}:{hs[D]}" for D in first[start:start + 10]))
    print("  class number 1:", [D for D in sorted(discs, reverse=True)
                                if hs[D] == 1])
    print("  forms of D = -20 (Q(sqrt-5)):", reduced_forms(-20))
    print(f"  largest h in range: {max(hs.values())}")
    print("Fundamental units of Z[sqrt d] (x + y sqrt d, norm x^2 - d y^2):")
    for d in (2, 3, 7, 19, 31, 43, 46, 94):
        x, y, nrm = fundamental_unit(d)
        print(f"  d = {d:>2}: {x} + {y} sqrt{d}  (norm {nrm:+d})")
    print()
    print("Epistemic status: exact integer computations, exhaustive for the")
    print("stated discriminants. That -163 is the last D with h(D) = 1 is the")
    print("Baker-Heegner-Stark theorem; the computation only covers |D| <= 200.")


if __name__ == "__main__":
    main()
