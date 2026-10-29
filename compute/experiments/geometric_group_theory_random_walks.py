"""Random walks see amenability: Kesten's criterion, computed exactly.

Simple random walk on a Cayley graph steps to a uniformly random neighbour.
Let p(2n) be the probability of being back at the start after 2n steps.

* On Z^2, p(2n) = (C(2n, n) / 4^n)^2, which decays like 1/(pi n): slower
  than any exponential, so p(2n)^(1/2n) -> 1.
* On the free group F_2 (the 4-regular tree), the distance from the start is
  a birth-death chain: from distance k >= 1 it goes up with probability 3/4
  and down with probability 1/4. We compute p(2n) exactly with fractions;
  p(2n)^(1/2n) tends to sqrt(3)/2 = 0.866..., the spectral radius.

Kesten's theorem (1959): a finitely generated group is amenable exactly when
the spectral radius is 1. Exact rational arithmetic for finitely many n; the
limits are theorems, approached here numerically.
"""

import math
from fractions import Fraction

EXPERIMENT = {
    "id": "geometric_group_theory_random_walks",
    "title": "Return probabilities of random walks: Z^2 versus the free group",
    "evidence": ["exact", "numerical"],
    "lessons": ["geometric-group-theory"],
    "summary": (
        "Computes the exact probability that simple random walk returns to its "
        "start after 2n steps on Z^2 (closed formula, checked against a direct "
        "count) and on the 4-regular tree, the Cayley graph of the free group "
        "F_2 (exact birth-death recursion). The n-th roots approach 1 and "
        "sqrt(3)/2, illustrating Kesten's amenability criterion; exact for "
        "finitely many n, the limits themselves are theorems."
    ),
    "packages": [],
}


def z2_return(n):
    """Exact return probability after 2n steps of simple random walk on Z^2."""
    return Fraction(math.comb(2 * n, n), 4 ** n) ** 2


def z2_return_by_counting(n):
    """The same probability by counting all walks of length 2n (small n)."""
    counts = {(0, 0): 1}
    for _ in range(2 * n):
        new = {}
        for (x, y), c in counts.items():
            for p in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
                new[p] = new.get(p, 0) + c
        counts = new
    return Fraction(counts.get((0, 0), 0), 4 ** (2 * n))


def tree_return(n, degree=4):
    """Exact return probability after 2n steps on the degree-regular tree."""
    up = Fraction(degree - 1, degree)
    down = Fraction(1, degree)
    dist = {0: Fraction(1)}
    for _ in range(2 * n):
        new = {}
        for k, pr in dist.items():
            if k == 0:
                new[1] = new.get(1, 0) + pr
            else:
                new[k + 1] = new.get(k + 1, 0) + pr * up
                new[k - 1] = new.get(k - 1, 0) + pr * down
        dist = new
    return dist.get(0, Fraction(0))


def nth_root(p, n):
    """p^(1/2n) as a float, computed through logarithms."""
    return math.exp(math.log(p) / (2 * n))


def main():
    print("Probability p(2n) of being back at the start after 2n steps")
    print("  2n    Z^2: p(2n)  p^(1/2n)  pi*n*p     F_2: p(2n)  p^(1/2n)")
    for n in (1, 2, 5, 10, 20, 40, 80):
        pz, pt = z2_return(n), tree_return(n)
        print(f"{2 * n:4d}  {float(pz):11.3e}  {nth_root(pz, n):8.5f}"
              f"  {math.pi * n * float(pz):6.4f}  {float(pt):11.3e}"
              f"  {nth_root(pt, n):8.5f}")
    print(f"Spectral radius of F_2 (Kesten): sqrt(3)/2 = {math.sqrt(3) / 2:.5f}")
    print(f"Formula for Z^2 checked by counting walks up to 2n = 12: "
          f"{all(z2_return(n) == z2_return_by_counting(n) for n in range(7))}")
    print(f"p(2) on the tree is exactly {tree_return(1)} (go out, come back).")
    print()
    print("Epistemic status: every p(2n) is an exact rational number. The")
    print("columns show Z^2 returning polynomially often (pi*n*p -> 1) and the")
    print("tree exponentially rarely, with n-th roots creeping towards 1 and")
    print("sqrt(3)/2. Finitely many n prove no limit: the limits are Kesten's")
    print("theorems; the roots converge slowly (corrections like n^(-c/n)).")


if __name__ == "__main__":
    main()
