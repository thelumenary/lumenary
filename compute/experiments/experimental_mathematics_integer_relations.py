"""Rediscovering the Bailey-Borwein-Plouffe formula, and using it.

The constants S_j = sum_k 16^-k / (8k + j), j = 1..8, and pi are computed to
60 digits with exact rational arithmetic (pi by Machin's formula). The PSLQ
integer-relation algorithm (Ferguson and Bailey), implemented here with
Python's decimal module, finds the relation pi = 4 S_1 - 2 S_4 - S_5 - S_6,
which is then re-checked at 100 digits. Two cautionary runs follow: with only
8 digits PSLQ "finds" a spurious relation for (pi, e, 1), and at 40 digits it
only bounds the size of any relation. Finally the formula is used to compute
hexadecimal digits of pi far after the point without the earlier ones, and
these are compared with an independent exact computation. A found relation is
numerical evidence; the lesson gives the proof.
"""

from decimal import Decimal, localcontext, ROUND_HALF_EVEN
from fractions import Fraction
import math

EXPERIMENT = {
    "id": "experimental_mathematics_integer_relations",
    "title": "PSLQ rediscovers the BBP formula for pi",
    "evidence": ["numerical", "exact"],
    "lessons": ["experimental-mathematics"],
    "summary": (
        "Runs the PSLQ integer-relation algorithm on pi and eight BBP-type sums "
        "computed to 60 digits, recovering pi = 4S1 - 2S4 - S5 - S6, rechecked at "
        "100 digits. Shows a spurious relation at low precision and a PSLQ lower "
        "bound when no relation is found, then extracts hexadecimal digits of pi "
        "at position 5001 with the BBP formula and checks them against exact "
        "integer arithmetic. Numerical evidence; the proof is in the lesson."
    ),
    "packages": [],
}

HEX = "0123456789ABCDEF"


def arctan_inv(x, scale):
    """floor-ish of arctan(1/x) * scale with integer arithmetic (error < terms)."""
    total = term = scale // x
    x2, k, sign = x * x, 1, -1
    while term:
        term //= x2
        total += sign * (term // (2 * k + 1))
        sign, k = -sign, k + 1
    return total


def pi_fraction(digits):
    """pi to about `digits` decimal digits (Machin: pi = 16 atan 1/5 - 4 atan 1/239)."""
    scale = 10 ** (digits + 10)
    return Fraction(4 * (4 * arctan_inv(5, scale) - arctan_inv(239, scale)), scale)


def e_fraction(digits):
    """e to well beyond `digits` digits, as an exact partial sum of 1/k!."""
    terms = 10
    while math.lgamma(terms + 1) / math.log(10) < digits + 5:
        terms += 5
    return sum(Fraction(1, math.factorial(k)) for k in range(terms))


def bbp_sum(j, digits):
    """S_j = sum_k 16^-k / (8k + j), truncated with error below 10^-digits."""
    terms = int(digits / 1.2) + 5
    return sum(Fraction(1, 16 ** k * (8 * k + j)) for k in range(terms))


def pslq(xs, digits, max_norm, max_iter=1000):
    """PSLQ on the reals xs (given as Fractions) at `digits` digits.

    Returns (relation or None, iterations, bound): if a relation is found it is
    an integer vector; otherwise every relation has norm at least `bound`.
    """
    n = len(xs)
    with localcontext() as ctx:
        ctx.prec = digits + 10
        x = [Decimal(f.numerator) / Decimal(f.denominator) for f in xs]
        eps = Decimal(10) ** (2 - digits)
        gamma = (Decimal(4) / 3).sqrt()
        A = [[int(i == j) for j in range(n)] for i in range(n)]
        B = [[int(i == j) for j in range(n)] for i in range(n)]
        s = [sum((v * v for v in x[k:]), Decimal(0)).sqrt() for k in range(n)]
        y = [v / s[0] for v in x]
        s = [v / s[0] for v in s]
        H = [[Decimal(0)] * (n - 1) for _ in range(n)]
        for i in range(n):
            if i < n - 1:
                H[i][i] = s[i + 1] / s[i]
            for j in range(min(i, n - 1)):
                H[i][j] = -y[i] * y[j] / (s[j] * s[j + 1])

        def reduce(i, j):
            t = int((H[i][j] / H[j][j]).to_integral_value(ROUND_HALF_EVEN))
            if t:
                y[j] += t * y[i]
                for k in range(j + 1):
                    H[i][k] -= t * H[j][k]
                for k in range(n):
                    A[i][k] -= t * A[j][k]
                    B[k][j] += t * B[k][i]

        for i in range(1, n):
            for j in range(i - 1, -1, -1):
                reduce(i, j)
        bound = Decimal(0)
        for it in range(1, max_iter + 1):
            m = max(range(n - 1), key=lambda i: gamma ** (i + 1) * abs(H[i][i]))
            y[m], y[m + 1] = y[m + 1], y[m]
            A[m], A[m + 1] = A[m + 1], A[m]
            H[m], H[m + 1] = H[m + 1], H[m]
            for row in B:
                row[m], row[m + 1] = row[m + 1], row[m]
            if m < n - 2:
                t0 = (H[m][m] ** 2 + H[m][m + 1] ** 2).sqrt()
                t1, t2 = H[m][m] / t0, H[m][m + 1] / t0
                for i in range(m, n):
                    t3, t4 = H[i][m], H[i][m + 1]
                    H[i][m] = t1 * t3 + t2 * t4
                    H[i][m + 1] = -t2 * t3 + t1 * t4
            for i in range(m + 1, n):
                for j in range(min(i - 1, m + 1), -1, -1):
                    reduce(i, j)
            jmin = min(range(n), key=lambda j: abs(y[j]))
            if abs(y[jmin]) < eps:
                rel = [B[k][jmin] for k in range(n)]
                sign = 1 if next(c for c in rel if c) > 0 else -1
                return [sign * c for c in rel], it, None
            bound = 1 / max(abs(H[i][i]) for i in range(n - 1))
            if bound > max_norm:
                break
        return None, it, float(bound)


def format_combination(rel):
    """Write -(rel_1 S_1 + ... + rel_8 S_8) as text, e.g. '4 S_1 - 2 S_4'."""
    text = ""
    for k, c in enumerate(rel):
        coeff = -c
        if k == 0 or coeff == 0:
            continue
        sign = "-" if coeff < 0 else "+"
        size = "" if abs(coeff) == 1 else f"{abs(coeff)} "
        text += f" {sign} {size}S_{k}"
    text = text.strip()
    return text[2:] if text.startswith("+ ") else text


def residual(rel, xs):
    """|sum rel_i * x_i| computed exactly from the Fractions xs."""
    return abs(sum(c * v for c, v in zip(rel, xs)))


def bbp_hex_digits(d, count):
    """Hex digits of pi at positions d+1, ..., d+count (BBP digit extraction)."""
    def frac_series(j):
        s = 0.0
        for k in range(d + 1):
            s = (s + pow(16, d - k, 8 * k + j) / (8 * k + j)) % 1.0
        k = d + 1
        while True:
            term = 16.0 ** (d - k) / (8 * k + j)
            if term < 1e-17:
                return s
            s, k = s + term, k + 1

    x = (4 * frac_series(1) - 2 * frac_series(4)
         - frac_series(5) - frac_series(6)) % 1.0
    out = ""
    for _ in range(count):
        x *= 16
        digit = int(x)
        out += HEX[digit]
        x -= digit
    return out


def exact_hex_digits(d, count):
    """The same digits from an exact integer computation (Machin, base 16)."""
    guard = 8
    scale = 16 ** (d + count + guard)
    pi_scaled = 4 * (4 * arctan_inv(5, scale) - arctan_inv(239, scale))
    block = (pi_scaled // 16 ** guard) % 16 ** count
    return format(block, "X").rjust(count, "0")


def main():
    digits = 60
    xs = [pi_fraction(digits)] + [bbp_sum(j, digits) for j in range(1, 9)]
    rel, its, _ = pslq(xs, digits, max_norm=10 ** 12)
    print("PSLQ on (pi, S_1, ..., S_8) at 60 digits, "
          "S_j = sum_k 16^-k/(8k+j):")
    print(f"  relation after {its} iterations: {tuple(rel)}")
    print(f"  i.e. pi = {format_combination(rel)}")
    xs100 = [pi_fraction(100)] + [bbp_sum(j, 100) for j in range(1, 9)]
    print("  residual with 100-digit values: "
          f"{float(residual(rel, xs100)):.1e}")
    print()
    low = [pi_fraction(8), e_fraction(8), Fraction(1)]
    fake, _, _ = pslq(low, 8, max_norm=10 ** 6)
    high = [pi_fraction(40), e_fraction(40), Fraction(1)]
    print(f"(pi, e, 1) at 8 digits: 'relation' {tuple(fake)}, but at 40 digits")
    print(f"  its residual is {float(residual(fake, high)):.1e}: spurious.")
    none, its, bound = pslq(high, 40, max_norm=10 ** 10)
    print(f"(pi, e, 1) at 40 digits: no relation; after {its} iterations every")
    print(f"  integer relation would need norm > {bound:.1e}.")
    print()
    d = 5000
    fast, exact = bbp_hex_digits(d, 8), exact_hex_digits(d, 8)
    print(f"Hex digits of pi after the point: {bbp_hex_digits(0, 8)} ...")
    print(f"Positions {d + 1}-{d + 8} by BBP digit extraction: {fast}")
    print(f"Same positions by exact integer arithmetic:      {exact}")
    print()
    print("Epistemic status: the relation is numerical evidence (60 digits, with")
    print("the residual rechecked at 100); its proof is in the lesson. The 'no")
    print("relation' bound is PSLQ's guarantee only if 40 digits were enough;")
    print("whether pi + e is irrational is an open problem. The hex digits agree")
    print("between two independent methods: an exact check of those 8 digits.")


if __name__ == "__main__":
    main()
