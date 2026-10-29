"""The harmonic series: terms that shrink to 0, sums that never stop growing.

Oresme's grouping says the block 1/(2^k + 1) + ... + 1/2^(k+1) is at least 1/2;
we compute these blocks exactly with fractions. Then, with 40-digit decimal
arithmetic, we find the first n with H_n = 1 + 1/2 + ... + 1/n > t for
t = 1, ..., 10 (H_n first exceeds 10 at n = 12367) and compare H_n with
ln n + 0.5772 (Euler's constant). By contrast, 1 + 1/4 + 1/9 + ... stays
below 2.
"""

import math
from decimal import Decimal, localcontext
from fractions import Fraction

EXPERIMENT = {
    "id": "sequences_series_harmonic",
    "title": "The harmonic series grows without bound, slowly",
    "evidence": ["exact", "numerical"],
    "lessons": ["sequences-series"],
    "summary": (
        "Computes Oresme's blocks of the harmonic series exactly (each at least "
        "1/2), finds the first n with 1 + 1/2 + ... + 1/n > t for t = 1..10 using "
        "40-digit decimals (n = 12367 for t = 10), compares with ln n + 0.5772, "
        "and contrasts the sum of 1/n^2, which stays below 2. Finite sums show "
        "slow growth; divergence is proved in the lesson."
    ),
    "packages": [],
}

#: Euler's constant gamma, to 16 digits (used only for comparison).
EULER_GAMMA = 0.5772156649015329


def oresme_block(k):
    """1/(2^k + 1) + ... + 1/2^(k+1), exactly (2^k terms)."""
    if k < 0:
        raise ValueError("k must be non-negative")
    return sum(Fraction(1, j) for j in range(2 ** k + 1, 2 ** (k + 1) + 1))


def harmonic_exact(n):
    """H_n = 1 + 1/2 + ... + 1/n as a Fraction (for small n)."""
    return sum((Fraction(1, j) for j in range(1, n + 1)), Fraction(0))


def first_exceeding(targets):
    """For each target t (increasing), the least n with H_n > t.

    Uses Decimal with 40 significant digits: after 10^5 additions the
    accumulated rounding error is far below the gaps 1/n near the answers.
    """
    answers = []
    with localcontext() as ctx:
        ctx.prec = 40
        total, n = Decimal(0), 0
        for t in targets:
            while total <= t:
                n += 1
                total += Decimal(1) / n
            answers.append(n)
    return answers


def basel_partial(n):
    """1 + 1/4 + ... + 1/n^2 in floating point (math.fsum)."""
    return math.fsum(1.0 / (j * j) for j in range(1, n + 1))


def main():
    print("Oresme's blocks (exact): each block of 2^k terms is at least 1/2")
    for k in range(5):
        block = oresme_block(k)
        terms = f"1/{2 ** k + 1} + ... + 1/{2 ** (k + 1)}" if k else "1/2"
        print(f"  k = {k}: {terms} = {float(block):.4f}"
              f"  >= 1/2: {block >= Fraction(1, 2)}")
    print("So H(2^m) >= 1 + m/2: the partial sums pass every bound.")
    print()
    targets = list(range(1, 11))
    print("t    first n with H_n > t    ln n + gamma")
    for t, n in zip(targets, first_exceeding(targets)):
        print(f"{t:2d}   {n:12d}             {math.log(n) + EULER_GAMMA:.4f}")
    print("The terms 1/n tend to 0, yet the sums still reach any height -")
    print("it takes roughly e^(t - 0.58) terms to reach height t.")
    print()
    for n in [10, 1000, 100000]:
        print(f"1 + 1/4 + ... + 1/{n}^2 = {basel_partial(n):.6f}   (< 2)")
    print(f"pi^2/6 = {math.pi ** 2 / 6:.6f}, Euler's value of the whole sum")
    print()
    print("Epistemic status: the blocks are exact for k <= 4 (the lesson")
    print("proves the bound for all k); the first-exceeding table uses")
    print("40-digit decimals, numerical but with error far below 1/n; the")
    print("ln n + gamma column is an approximation. No finite table proves")
    print("divergence: the grouping argument does.")


if __name__ == "__main__":
    main()
