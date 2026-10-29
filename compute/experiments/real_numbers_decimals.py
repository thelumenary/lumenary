"""Decimal expansions: fractions repeat, sqrt(2) and pi need not.

Long division of p by q can only meet q different remainders, so the digits
of a fraction must eventually repeat, with a period of at most q - 1 digits.
The experiment computes exact expansions (pre-period and period) of a few
fractions, then the first 40 digits of sqrt(2) (exactly, with integer square
roots) and of pi (exactly, with Machin's formula in integer arithmetic), and
compares pi with the famous approximations 22/7 and 355/113.
"""

import math

EXPERIMENT = {
    "id": "real_numbers_decimals",
    "title": "Repeating and non-repeating decimals",
    "evidence": ["exact", "numerical"],
    "lessons": ["real-numbers"],
    "summary": (
        "Finds the exact pre-period and period of decimal expansions of fractions "
        "by tracking remainders in long division, then computes 40 correct "
        "digits of sqrt(2) and pi with integer arithmetic and shows where 22/7 "
        "and 355/113 part company with pi. Finitely many digits never prove "
        "irrationality: that needs a proof."
    ),
    "packages": [],
}


def decimal_expansion(p, q):
    """Return (whole part, pre-period digits, period digits) of p/q >= 0.

    Long division: a remainder that comes back starts the repeating block.
    A terminating decimal has period "0".
    """
    if q <= 0 or p < 0:
        raise ValueError("need p >= 0 and q > 0")
    whole, r = divmod(p, q)
    digits, seen = [], {}
    while r not in seen:
        seen[r] = len(digits)
        d, r = divmod(10 * r, q)
        digits.append(str(d))
    start = seen[r]
    return whole, "".join(digits[:start]), "".join(digits[start:])


def sqrt_digits(n, k):
    """The first k decimal digits of sqrt(n) after the point (truncated)."""
    root = math.isqrt(n * 10 ** (2 * k))
    return str(root)[-k:] if k else ""


def arctan_inv(x, scale):
    """scale * arctan(1/x) for an integer x > 1, by the alternating series."""
    total, term, k, sign = 0, scale // x, 1, 1
    while term:
        total += sign * (term // k)
        term //= x * x
        k += 2
        sign = -sign
    return total


def pi_digits(k):
    """The first k decimal digits of pi after the point (truncated).

    Machin (1706): pi = 16 arctan(1/5) - 4 arctan(1/239); 10 guard digits.
    """
    scale = 10 ** (k + 10)
    pi_scaled = 16 * arctan_inv(5, scale) - 4 * arctan_inv(239, scale)
    return str(pi_scaled // 10 ** 10)[1:k + 1]


def fraction_digits(p, q, k):
    """The first k digits of p/q after the point."""
    return str((p % q) * 10 ** k // q).zfill(k)


def agreement(a, b):
    """Number of leading digits two digit strings share."""
    n = 0
    while n < min(len(a), len(b)) and a[n] == b[n]:
        n += 1
    return n


def main():
    print("Fractions: long division must repeat (period at most q - 1).")
    for p, q in [(3, 8), (1, 7), (5, 12), (22, 7), (1, 97)]:
        whole, pre, per = decimal_expansion(p, q)
        shown = per if len(per) <= 24 else per[:24] + "..."
        print(f"  {p}/{q} = {whole}.{pre}({shown})  period {len(per)}")
    print()
    root2 = sqrt_digits(2, 40)
    pi = pi_digits(40)
    print(f"sqrt(2) = 1.{root2}...")
    print(f"pi      = 3.{pi}...")
    for p, q in [(22, 7), (355, 113)]:
        digits = fraction_digits(p, q, 40)
        same = agreement(pi, digits)
        print(f"{p}/{q} = 3.{digits[:12]}...  agrees with pi to {same} decimals")
    print("These digits show no repeating block, but finitely many digits")
    print("decide nothing: 1/97 needs 96 digits before its block repeats.")
    print()
    print("Epistemic status: all digits are exact integer computations (the")
    print("pi digits rely on Machin's formula with 10 guard digits). Finding no")
    print("repetition in finitely many digits proves nothing; sqrt(2) is")
    print("irrational by the lesson's proof, and pi by Lambert's (1761).")


if __name__ == "__main__":
    main()
