"""Tor and Ext of cyclic groups from projective resolutions, two ways.

Z/m has the free resolution 0 -> Z --m--> Z -> Z/m -> 0. Tensoring with Z/n
gives the complex Z/n --m--> Z/n, whose homology is Tor_1 (kernel) and
Tor_0 = Z/m (x) Z/n (cokernel); applying Hom(-, Z/n) gives the same map, whose
kernel is Hom(Z/m, Z/n) and cokernel Ext^1(Z/m, Z/n). We count kernels and
cokernels by brute force and compare with gcd(m, n). Then we redo Tor_1 with
a different, non-minimal resolution 0 -> Z^2 --A--> Z^2 -> Z/m -> 0 and check
that the answer does not change, as the comparison theorem predicts.
Exact finite arithmetic, exhaustive in the stated range.
"""

from itertools import product
from math import gcd

EXPERIMENT = {
    "id": "homological_algebra_tor_ext",
    "title": "Tor and Ext of cyclic groups from resolutions",
    "evidence": ["exact", "exhaustive-finite"],
    "lessons": ["homological-algebra"],
    "summary": (
        "For all 1 <= m, n <= 20 computes Tor_0, Tor_1, Hom and Ext^1 of Z/m "
        "and Z/n as kernels and cokernels of multiplication by m on Z/n, "
        "checks that each has gcd(m, n) elements, and recomputes Tor_1 from a "
        "second, non-minimal free resolution of Z/m to confirm independence of "
        "the resolution. Exhaustive in that range; the lesson proves both facts."
    ),
    "packages": [],
}


def kernel_size(m, n):
    """Number of x in Z/n with m x = 0."""
    return sum(1 for x in range(n) if m * x % n == 0)


def cokernel_size(m, n):
    """|Z/n / m(Z/n)|."""
    return n // len({m * x % n for x in range(n)})


def tor1_from_matrix(a, n):
    """Kernel size of the integer matrix a (2x2) acting on (Z/n)^2."""
    count = 0
    for x, y in product(range(n), repeat=2):
        u = (a[0][0] * x + a[0][1] * y) % n
        v = (a[1][0] * x + a[1][1] * y) % n
        count += u == 0 and v == 0
    return count


def second_resolution(m):
    """A 2x2 integer matrix with cokernel Z/m: relations (m, 0) and (3, 1)."""
    return [[m, 3], [0, 1]]


def main():
    limit = 20
    pairs = [(m, n) for m in range(1, limit + 1) for n in range(1, limit + 1)]
    ker_ok = sum(kernel_size(m, n) == gcd(m, n) for m, n in pairs)
    cok_ok = sum(cokernel_size(m, n) == gcd(m, n) for m, n in pairs)
    alt_ok = sum(tor1_from_matrix(second_resolution(m), n) == gcd(m, n)
                 for m, n in pairs)
    print(f"All {len(pairs)} pairs 1 <= m, n <= {limit}; Z/n (x) - and "
          "Hom(-, Z/n) give Z/n --m--> Z/n:")
    print(f"  kernel = Tor_1 = Hom(Z/m, Z/n) has gcd(m, n) elements:  {ker_ok}")
    print(f"  cokernel = Tor_0 = Ext^1(Z/m, Z/n) has gcd(m, n) elements: "
          f"{cok_ok}")
    print(f"  Tor_1 from the resolution Z^2 --A--> Z^2, A = [[m, 3], [0, 1]]: "
          f"{alt_ok}")
    print("Examples (|kernel|, |cokernel|):")
    for m, n in [(4, 6), (2, 2), (3, 5), (12, 18)]:
        print(f"  m = {m}, n = {n}: {kernel_size(m, n)}, {cokernel_size(m, n)}")
    print("Ext^1(Z/n, Z) = Z / nZ, so Ext^1(Z/2, Z) has 2 elements: the split")
    print("  extension Z + Z/2 and the non-split 0 -> Z --2--> Z -> Z/2 -> 0.")
    print()
    print("Epistemic status: exact and exhaustive for m, n <= 20, using one "
          "particular\nsecond resolution. It illustrates the comparison "
          "theorem and the formula\nTor_1(Z/m, Z/n) = Z/gcd(m, n); both are "
          "proved in the lesson for all m, n.")


if __name__ == "__main__":
    main()
