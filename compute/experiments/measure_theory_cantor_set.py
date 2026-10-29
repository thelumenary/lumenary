"""The Cantor set: uncountably many points, total length zero.

Builds the stages C_n of the middle-thirds Cantor set with exact rational
arithmetic: C_n is a union of 2^n closed intervals of total length (2/3)^n.
It then checks that 1/4 survives every stage computed although it is never an
endpoint, and shows the injection from 0/1-sequences into the Cantor set
(binary digit b -> ternary digit 2b) that makes it uncountable. Exact
arithmetic for finitely many stages; the limits are the lesson's proofs.
"""

from fractions import Fraction

EXPERIMENT = {
    "id": "measure_theory_cantor_set",
    "title": "The Cantor set: uncountable but of measure zero",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["measure-theory"],
    "summary": (
        "Computes the stages C_n of the Cantor set exactly with fractions: 2^n "
        "intervals of total length (2/3)^n, so the Cantor set has outer measure "
        "at most (2/3)^n for every n. Checks that 1/4 lies in every stage "
        "computed without being an endpoint, and that distinct 0/1 strings give "
        "distinct points (the injection behind uncountability). Finite stages "
        "only; the limiting statements are proved in the lesson."
    ),
    "packages": [],
}


def cantor_stage(n):
    """The 2^n closed intervals (a, b) of the n-th stage C_n, as Fractions."""
    if n < 0:
        raise ValueError("n must be non-negative")
    intervals = [(Fraction(0), Fraction(1))]
    for _ in range(n):
        new = []
        for a, b in intervals:
            third = (b - a) / 3
            new.append((a, a + third))
            new.append((b - third, b))
        intervals = new
    return intervals


def total_length(intervals):
    """Sum of the lengths of disjoint intervals."""
    return sum((b - a for a, b in intervals), Fraction(0))


def in_stage(x, n):
    """True if the rational x lies in C_n (checked by the ternary rule)."""
    x = Fraction(x)
    if not 0 <= x <= 1:
        return False
    for _ in range(n):
        if Fraction(1, 3) < x < Fraction(2, 3):
            return False
        x = 3 * x if x <= Fraction(1, 3) else 3 * x - 2
    return True


def ternary_digits(x, k):
    """The first k ternary digits of a rational x in [0, 1)."""
    x = Fraction(x)
    digits = []
    for _ in range(k):
        x *= 3
        d = int(x)
        digits.append(d)
        x -= d
    return digits


def endpoints(n):
    """All endpoints of the intervals of C_n."""
    return {e for interval in cantor_stage(n) for e in interval}


def bits_to_cantor_point(bits):
    """The point sum 2*b_i / 3^i of the Cantor set coded by the bits b_i."""
    return sum((Fraction(2 * b, 3 ** (i + 1)) for i, b in enumerate(bits)),
               Fraction(0))


def first_stage_below(threshold):
    """Least n with (2/3)^n < threshold."""
    n, length = 0, Fraction(1)
    while length >= threshold:
        n, length = n + 1, length * Fraction(2, 3)
    return n


def main():
    print("Stages of the Cantor set (exact arithmetic)")
    print(f"{'n':>3} {'intervals':>10} {'total length':>20} {'decimal':>10}")
    for n in [0, 1, 2, 3, 5, 10, 20]:
        stage = cantor_stage(n) if n <= 12 else None
        length = total_length(stage) if stage else Fraction(2, 3) ** n
        count = len(stage) if stage else 2 ** n
        print(f"{n:>3} {count:>10} {str(length):>20} {float(length):>10.6f}")
    print(f"Length below 1/1000 from stage n = {first_stage_below(Fraction(1, 1000))}.")
    print()
    quarter = Fraction(1, 4)
    print("Is 1/4 in the Cantor set?")
    print("  ternary digits of 1/4:", "".join(map(str, ternary_digits(quarter, 12))),
          "...")
    print(f"  in every stage C_n for n <= 40: {all(in_stage(quarter, n) for n in range(41))}")
    print(f"  an endpoint of some C_n, n <= 12: {quarter in endpoints(12)}")
    print("  (endpoints have denominators 3^n, and 4 is not a power of 3)")
    print()
    strings = [[(m >> i) & 1 for i in range(10)] for m in range(2 ** 10)]
    points = {bits_to_cantor_point(s) for s in strings}
    print("0/1 strings -> Cantor points by b -> ternary digit 2b:")
    print(f"  {len(strings)} strings of length 10 give {len(points)} distinct points,")
    print(f"  all in C_10: {all(in_stage(p, 10) for p in points)}")
    print()
    print("Epistemic status: exact rational arithmetic for finitely many stages")
    print("and strings. It shows that C is covered by intervals of total length")
    print("(2/3)^n for the n computed. That C is null (it lies in every C_n) and")
    print("that the injection on infinite sequences makes it uncountable are the")
    print("lesson's proofs, not consequences of this finite check.")


if __name__ == "__main__":
    main()
