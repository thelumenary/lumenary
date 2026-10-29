"""When may a limit pass through an integral? Four sequences, exactly.

For four classic sequences of functions we compute the integrals exactly
(fractions) and follow the values at a fixed point: escaping mass
n * 1_(0, 1/n), a travelling bump 1_[n, n+1], the dominated sequence x^n on
[0, 1], and the "typewriter" sequence of shrinking dyadic intervals. The first
two converge pointwise to 0 while their integrals stay 1; the third obeys the
dominated convergence theorem; the fourth converges in L^1 but at no point.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "measure_theory_convergence_modes",
    "title": "Limits and integrals: four sequences of functions",
    "evidence": ["exact", "counterexample"],
    "lessons": ["measure-theory"],
    "summary": (
        "Computes exact integrals and point values for four sequences: escaping "
        "mass, a travelling bump, x^n on [0, 1] and the typewriter sequence. The "
        "first two are counterexamples to swapping limit and integral without a "
        "dominating function; the typewriter converges in L^1 yet its values at "
        "x = 1/3 keep returning to 1. Finitely many terms are computed; the "
        "limiting behaviour is proved in the lesson."
    ),
    "packages": [],
}


def escaping(n, x):
    """f_n(x) = n on the open interval (0, 1/n), else 0."""
    x = Fraction(x)
    return n if 0 < x < Fraction(1, n) else 0


def escaping_integral(n):
    """The integral of f_n: height n times length 1/n."""
    return n * Fraction(1, n)


def bump(n, x):
    """g_n(x) = 1 on [n, n + 1], else 0."""
    return 1 if n <= Fraction(x) <= n + 1 else 0


def power_integral(n):
    """The integral of x^n over [0, 1]."""
    return Fraction(1, n + 1)


def typewriter_interval(k):
    """For k >= 1 write k = 2^m + j with 0 <= j < 2^m: the interval
    [j / 2^m, (j + 1) / 2^m]."""
    if k < 1:
        raise ValueError("k must be at least 1")
    m = k.bit_length() - 1
    j = k - 2 ** m
    return Fraction(j, 2 ** m), Fraction(j + 1, 2 ** m)


def typewriter(k, x):
    """T_k(x) = indicator of the k-th typewriter interval."""
    a, b = typewriter_interval(k)
    return 1 if a <= Fraction(x) <= b else 0


def typewriter_integral(k):
    """The integral of T_k is the length of its interval."""
    a, b = typewriter_interval(k)
    return b - a


def hits(k_max, x):
    """The k <= k_max with T_k(x) = 1."""
    return [k for k in range(1, k_max + 1) if typewriter(k, x) == 1]


def main():
    ns = [1, 2, 10, 100, 1000]
    print("integrals for n =", ns)
    print("  escaping mass n*1_(0,1/n):",
          [str(escaping_integral(n)) for n in ns])
    print("  x^n on [0, 1]            :", [str(power_integral(n)) for n in ns])
    print("values at x = 1/10 for n = 1..12 (escaping mass):")
    print("  ", [escaping(n, Fraction(1, 10)) for n in range(1, 13)])
    print("values at x = 5/2 for n = 0..6 (travelling bump, integral 1):")
    print("  ", [bump(n, Fraction(5, 2)) for n in range(7)])
    print()
    print("Typewriter T_k, k = 2^m + j: the indicator of [j/2^m, (j+1)/2^m]")
    for k in [1, 2, 3, 4, 7, 8, 100, 1000]:
        a, b = typewriter_interval(k)
        print(f"  k = {k:>4}: [{a}, {b}], integral {typewriter_integral(k)}")
    third = Fraction(1, 3)
    h = hits(1023, third)
    print(f"  T_k(1/3) = 1 for {len(h)} values of k <= 1023, one per block:")
    print("  ", h)
    print("  so T_k(1/3) is 1 infinitely often and 0 infinitely often,")
    print("  but along k = 2^m:", [typewriter(2 ** m, third) for m in range(8)])
    print()
    print("Epistemic status: exact arithmetic on finitely many terms. The")
    print("escaping mass and travelling bump are genuine counterexamples (each")
    print("integral is exactly 1, and each point value is eventually 0, as the")
    print("lesson proves). The typewriter output illustrates, but does not prove,")
    print("that L^1 convergence implies only a.e. convergence of a subsequence.")


if __name__ == "__main__":
    main()
