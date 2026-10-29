"""Bernoulli numbers in stable homotopy: the image of J and exotic spheres.

Two classical theorems turn Bernoulli numbers into homotopy theory.

* Adams (with the Adams conjecture, proved by Quillen, Sullivan and
  Becker-Gottlieb): the image of the stable J-homomorphism in the stable stem
  pi_{4k-1}^s is cyclic of order m(2k) = denominator of B_{2k} / 4k.
* Kervaire-Milnor (1963): the group bP_{4k} of exotic (4k-1)-spheres that
  bound parallelisable manifolds has order
  2^(2k-2) (2^(2k-1) - 1) * numerator(4 |B_{2k}| / k), for k >= 2.

We compute the Bernoulli numbers exactly, evaluate both formulas, and compare
m(2k) with the known stable stems pi_3^s = Z/24, pi_7^s = Z/240,
pi_11^s = Z/504 and pi_15^s = Z/480 + Z/2 (Toda, 1962), which are quoted here,
not computed.
"""

from fractions import Fraction
from math import comb

EXPERIMENT = {
    "id": "stable_homotopy_theory_image_of_j",
    "title": "Bernoulli numbers, the image of J and exotic spheres",
    "evidence": ["exact"],
    "lessons": ["stable-homotopy-theory"],
    "summary": (
        "Computes Bernoulli numbers exactly and evaluates m(2k) = denominator of "
        "B_2k/4k, the order of the image of J in the stable stem pi_{4k-1}^s, and "
        "the Kervaire-Milnor order of bP_4k (28 exotic 7-spheres, 992, 8128). "
        "Compares m(2k) with the known stems pi_3^s, pi_7^s, pi_11^s, pi_15^s, "
        "which are quoted from the literature. Exact arithmetic; the theorems "
        "linking it to topology are cited."
    ),
    "packages": [],
}


def bernoulli_numbers(n):
    """B_0, ..., B_n (convention B_1 = -1/2), from sum_j C(m+1, j) B_j = 0."""
    b = [Fraction(1)]
    for m in range(1, n + 1):
        s = sum(comb(m + 1, j) * b[j] for j in range(m))
        b.append(-s / (m + 1))
    return b


def image_of_j_order(k, b):
    """m(2k): the denominator of B_{2k} / 4k."""
    return (b[2 * k] / (4 * k)).denominator


def bp_order(k, b):
    """Kervaire-Milnor order of bP_{4k}, k >= 2."""
    num = (4 * abs(b[2 * k]) / k).numerator
    return 2 ** (2 * k - 2) * (2 ** (2 * k - 1) - 1) * num


#: Known stable stems pi_{4k-1}^s (Toda 1962), as orders and descriptions.
KNOWN_STEMS = {1: (24, "Z/24"), 2: (240, "Z/240"), 3: (504, "Z/504"),
               4: (960, "Z/480 + Z/2")}


def main():
    b = bernoulli_numbers(16)
    print(" k  B_2k          m(2k) = den(B_2k/4k)  pi_(4k-1)^s (known)")
    for k in range(1, 9):
        m = image_of_j_order(k, b)
        known = KNOWN_STEMS.get(k)
        tail = f"{known[1]} ({known[0] // m} x |im J|)" if known else "-"
        print(f"{k:2d}  {str(b[2 * k]):12s}  {m:21d}  {tail}")
    print("Numerators such as 691 (B_12) and 3617 (B_16) reappear in |bP_4k|.")
    print()
    print("Exotic spheres bounding parallelisable manifolds (Kervaire-Milnor):")
    for k in range(2, 6):
        print(f"  |bP_{4 * k}| = {bp_order(k, b):>10d}"
              f"   (homotopy {4 * k - 1}-spheres)")
    print("Since pi_7^s = im J, all homotopy 7-spheres bound parallelisable")
    print("manifolds: S^7 has exactly 28 smooth structures up to orientation-")
    print("preserving diffeomorphism, Milnor's 1956 examples among them.")
    print()
    print("Epistemic status: the Bernoulli numbers and both formulas are exact")
    print("rational computations. That m(2k) is the order of the image of J,")
    print("and the Kervaire-Milnor count, are theorems cited from the literature;")
    print("the stable stems in the last column are quoted (Toda's computations),")
    print("not computed. Agreement is consistency, not proof.")


if __name__ == "__main__":
    main()
